//! Per-task state for `driver::worker`, which runs many tasks (a sweep's children) in one process. Every process-wide static
//! in church_bv is either a pure memo, whose value depends only on its key (configuration included), kept across tasks
//! (a `SharedMemo`, or one of the few on `task_state_is_classified`'s list), or task state: a `PerTask` or `PerTaskArc`,
//! rebuilt at its first read in each task. `task_state_is_classified` holds
//! every static to that rule (docs/tier-cycle.md, "A persistent worker").

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

/// A pure memo shared by a process's threads and kept across tasks: each value must depend only on its key, configuration
/// included. `task_state_is_classified` takes that on trust, so each static of this type says why at its declaration.
pub struct SharedMemo<K, V> {
    map: Mutex<Option<hashbrown::HashMap<K, V>>>,
}

impl<K: Eq + std::hash::Hash, V> SharedMemo<K, V> {
    pub const fn new() -> Self {
        SharedMemo { map: Mutex::new(None) }
    }
    fn lock(&self) -> std::sync::MutexGuard<'_, Option<hashbrown::HashMap<K, V>>> {
        self.map.lock().unwrap_or_else(|e| e.into_inner())
    }
    /// `f` on `key`'s value, built by `init` if absent; both run under the memo's lock.
    pub fn with<R>(&self, key: K, init: impl FnOnce() -> V, f: impl FnOnce(&mut V) -> R) -> R {
        f(self.lock().get_or_insert_with(Default::default).entry(key).or_insert_with(init))
    }
    /// `key`'s value, if built: with `insert`, for a value built unlocked.
    pub fn get(&self, key: &K) -> Option<V>
    where
        V: Clone,
    {
        self.lock().as_ref()?.get(key).cloned()
    }
    pub fn insert(&self, key: K, v: V) {
        self.lock().get_or_insert_with(Default::default).insert(key, v);
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

/// A key's value is built once and kept, across tasks too; `get` and `insert` reach the same map.
#[test]
fn shared_memo_builds_each_key_once() {
    let m: SharedMemo<u8, Vec<u8>> = SharedMemo::new();
    let builds = std::cell::Cell::new(0);
    let build = |k: u8| {
        builds.set(builds.get() + 1);
        vec![k]
    };
    assert_eq!(m.with(1, || build(1), |v| v.clone()), vec![1]);
    assert_eq!(m.with(1, || build(9), |v| { v.push(2); v.clone() }), vec![1, 2]);
    assert_eq!(builds.get(), 1);
    assert_eq!(m.get(&1), Some(vec![1, 2]));
    assert_eq!(m.get(&3), None);
    m.insert(3, vec![3]);
    assert_eq!(m.with(3, || build(3), |v| v.clone()), vec![3]);
    assert_eq!(builds.get(), 1);
}

/// The name of the process-wide mutable static declared on `line`, if any: `static mut`, or a static whose type mentions a
/// lock, a once-cell or an atomic, other than the classified kinds (`PerTask`, `PerTaskArc`, `SharedMemo`). Thread-locals in
/// church_bv hold `Cell`s and `RefCell`s, so they are not flagged (a lock in a thread-local would be, falsely). It cannot see
/// interior mutability behind any other struct's name (`static X: Counters`): no church_bv static is one.
fn flagged(line: &str) -> Option<&str> {
    let t = line.trim_start();
    let rest = ["pub(crate) static ", "pub static ", "static "].iter().find_map(|p| t.strip_prefix(p))?;
    let (is_mut, rest) = match rest.strip_prefix("mut ") {
        Some(r) => (true, r),
        None => (false, rest),
    };
    let (name, ty) = rest.split_once(':')?;
    let mutable = is_mut || ["Mutex", "RwLock", "Once", "LazyLock", "Atomic"].iter().any(|m| ty.contains(m));
    (mutable && !["PerTask", "SharedMemo"].iter().any(|k| ty.contains(k))).then_some(name.trim())
}

/// Every process-wide mutable static in church_bv is task state (`PerTask`, `PerTaskArc`), a `SharedMemo` or a pure memo on this list,
/// so a `driver::worker` task never sees another task's configuration or counters.
#[test]
fn task_state_is_classified() {
    const PURE: [(&str, &str, &str); 6] = [
        ("rewrite.rs", "TABLE", "the term table: interning is pure"),
        ("rewrite.rs", "CACHE", "promoted_rules parses a constant table"),
        ("lemma_cache.rs", "ID", "the running exe's identity"),
        ("task.rs", "TASK", "the task machinery"),
        ("task.rs", "TASK_ENV", "the task machinery"),
        ("driver.rs", "NONCE", "env_echo's per-process nonce, process-wide on purpose"),
    ];
    assert_eq!(flagged("    static X: std::sync::OnceLock<u8> = std::sync::OnceLock::new();"), Some("X"));
    assert_eq!(flagged("pub static Y: [std::sync::atomic::AtomicU64; 3] = x;"), Some("Y"));
    assert_eq!(flagged("static mut Z: u8 = 0;"), Some("Z"));
    assert_eq!(flagged("static W: PerTask<std::sync::Mutex<u8>> = PerTask::new();"), None);
    assert_eq!(flagged("static M: crate::task::SharedMemo<u8, std::sync::Arc<u8>> = SharedMemo::new();"), None);
    assert_eq!(flagged("    static T: std::cell::RefCell<u8> = Default::default();"), None);
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/church_bv");
    let mut bad = vec![];
    for entry in std::fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|e| e != "rs") {
            continue;
        }
        let file = path.file_name().unwrap().to_str().unwrap().to_string();
        for (i, line) in std::fs::read_to_string(&path).unwrap().lines().enumerate() {
            if let Some(name) = flagged(line) {
                if !PURE.iter().any(|p| p.0 == file && p.1 == name) {
                    bad.push(format!("{file}:{} {name}", i + 1));
                }
            }
        }
    }
    assert!(bad.is_empty(), "process-wide statics that are neither PerTask nor a listed pure memo: {bad:?}");
}
