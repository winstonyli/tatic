//! Process-wide memos for `driver::worker`, which runs many tasks (a sweep's children) in one process. A task's
//! configuration and outcome live in its `job::Setup`; every process-wide mutable static in church_bv is a pure memo, whose
//! value depends only on its key (configuration included), kept across tasks: a `SharedMemo`, or one of the few on
//! `task_state_is_classified`'s list. `task_state_is_classified` holds every static to that rule (docs/tier-cycle.md,
//! "A persistent worker").

use std::sync::Mutex;

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
/// lock, a once-cell or an atomic, other than a `SharedMemo`. Thread-locals in
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
    (mutable && !ty.contains("SharedMemo")).then_some(name.trim())
}

/// Every process-wide mutable static in church_bv is a `SharedMemo` or a pure memo on this list, so a `driver::worker` task
/// never sees another task's configuration or counters: those live in its `Setup`.
#[test]
fn task_state_is_classified() {
    const PURE: [(&str, &str, &str); 6] = [
        ("rewrite.rs", "TABLE", "the term table: interning is pure"),
        ("rewrite.rs", "CACHE", "promoted_rules parses a constant table"),
        ("lemma_cache.rs", "ID", "the running exe's identity"),
        ("driver.rs", "NONCE", "env_echo's per-process nonce, process-wide on purpose"),
        ("job.rs", "PROCESS_SETUP", "the one-test process's Setup; tasks build their own"),
        ("job.rs", "NEXT_JOB", "job ids, unique per process on purpose"),
    ];
    assert_eq!(flagged("    static X: std::sync::OnceLock<u8> = std::sync::OnceLock::new();"), Some("X"));
    assert_eq!(flagged("pub static Y: [std::sync::atomic::AtomicU64; 3] = x;"), Some("Y"));
    assert_eq!(flagged("static mut Z: u8 = 0;"), Some("Z"));
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
    assert!(bad.is_empty(), "process-wide statics that are neither a SharedMemo nor a listed pure memo: {bad:?}");
}
