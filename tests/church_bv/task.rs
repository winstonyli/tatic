//! Per-task state for `driver::worker`, which runs many tasks (a sweep's children) in one process. Every process-wide static
//! in church_bv is either a pure memo, whose value depends only on its key (configuration included), kept across tasks,
//! or task state: a `PerTask` or `PerTaskArc`, rebuilt at its first read in each task. `task_state_is_classified` holds
//! every static to that rule (docs/superpowers/specs/2026-10-15-sweep-worker-design.md).

use std::marker::PhantomData;
use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering::{Acquire, Relaxed, Release}};
use std::sync::{Arc, Mutex};

/// The task this process is running: 0 in a process that runs one test, bumped by `begin` before each worker task.
static TASK: AtomicUsize = AtomicUsize::new(0);
/// The current task's environment pairs, over the process's own (`rewrite::env_var`).
static TASK_ENV: Mutex<Vec<(String, String)>> = Mutex::new(Vec::new());

/// Starts a task whose environment is the process's with `env` over it: every `PerTask` and `PerTaskArc` is rebuilt at its
/// next read. Only `driver::worker` calls it, between tasks, with no task thread running.
pub fn begin(env: Vec<(String, String)>) {
    *TASK_ENV.lock().unwrap_or_else(|e| e.into_inner()) = env;
    TASK.fetch_add(1, Relaxed);
}

/// The current task's environment pairs (empty outside a worker).
pub fn task_env() -> Vec<(String, String)> {
    TASK_ENV.lock().unwrap_or_else(|e| e.into_inner()).clone()
}

/// A value built at its first read in each task (in a one-test process, once, like `OnceLock`). Each task's value is
/// leaked so reads can return `&'static`: keep `T` small (a sweep has about 170 tasks); `PerTaskArc` is for large values.
pub struct PerTask<T> {
    cur: AtomicPtr<(usize, T)>,
    init: Mutex<()>,
    _t: PhantomData<T>,
}

impl<T: Send + Sync + 'static> PerTask<T> {
    pub const fn new() -> Self {
        PerTask { cur: AtomicPtr::new(std::ptr::null_mut()), init: Mutex::new(()), _t: PhantomData }
    }
    /// This task's value, built by `init` at the task's first read. `init` must not read this same `PerTask`.
    pub fn get(&self, init: impl FnOnce() -> T) -> &'static T {
        self.get_at(TASK.load(Relaxed), init)
    }
    fn peek_at(&self, epoch: usize) -> Option<&'static T> {
        let p = self.cur.load(Acquire);
        // SAFETY: `cur` is null or a box leaked by `get_at`, never freed
        unsafe { p.as_ref() }.filter(|c| c.0 == epoch).map(|c| &c.1)
    }
    fn get_at(&self, epoch: usize, init: impl FnOnce() -> T) -> &'static T {
        if let Some(v) = self.peek_at(epoch) {
            return v;
        }
        let _guard = self.init.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(v) = self.peek_at(epoch) {
            return v;
        }
        let built: &'static mut (usize, T) = Box::leak(Box::new((epoch, init())));
        self.cur.store(built, Release);
        &built.1
    }
}

/// A `PerTask` for values too large to leak once per task: the first read in a new task replaces the old value, which drops
/// with its last `Arc`.
pub struct PerTaskArc<T> {
    cur: Mutex<Option<(usize, Arc<T>)>>,
}

impl<T> PerTaskArc<T> {
    pub const fn new() -> Self {
        PerTaskArc { cur: Mutex::new(None) }
    }
    /// This task's value, built by `init` at the task's first read (under this value's lock).
    pub fn get(&self, init: impl FnOnce() -> T) -> Arc<T> {
        self.get_at(TASK.load(Relaxed), init)
    }
    /// This task's value if this task built one, without building it.
    pub fn peek(&self) -> Option<Arc<T>> {
        self.peek_at(TASK.load(Relaxed))
    }
    fn peek_at(&self, epoch: usize) -> Option<Arc<T>> {
        self.cur.lock().unwrap_or_else(|e| e.into_inner()).as_ref().filter(|c| c.0 == epoch).map(|c| c.1.clone())
    }
    fn get_at(&self, epoch: usize, init: impl FnOnce() -> T) -> Arc<T> {
        let mut cur = self.cur.lock().unwrap_or_else(|e| e.into_inner());
        if let Some((e, v)) = cur.as_ref() {
            if *e == epoch {
                return v.clone();
            }
        }
        let v = Arc::new(init());
        *cur = Some((epoch, v.clone()));
        v
    }
}

/// Each epoch builds its own value once; `peek` sees only the current epoch's. Explicit epochs: bumping `TASK` here would
/// reset the counters of the suite's other tests, which run in this process at the same time.
#[test]
fn per_task_rebuilds_per_task() {
    let p: PerTask<usize> = PerTask::new();
    let builds = std::cell::Cell::new(0);
    let build = || {
        builds.set(builds.get() + 1);
        builds.get()
    };
    assert_eq!(p.peek_at(7), None);
    assert_eq!(*p.get_at(7, build), 1);
    assert_eq!(*p.get_at(7, build), 1);
    assert_eq!(p.peek_at(7), Some(&1));
    assert_eq!(p.peek_at(8), None);
    assert_eq!(*p.get_at(8, build), 2);
    assert_eq!(builds.get(), 2);

    let a: PerTaskArc<String> = PerTaskArc::new();
    assert!(a.peek_at(1).is_none());
    let first = Arc::downgrade(&a.get_at(1, || "one".into()));
    assert_eq!(*a.get_at(1, || "again".into()), "one");
    assert_eq!(a.peek_at(1).as_deref().map(String::as_str), Some("one"));
    assert!(a.peek_at(2).is_none());
    assert_eq!(*a.get_at(2, || "two".into()), "two");
    assert!(first.upgrade().is_none(), "the first epoch's value dropped when the second replaced it");
}
