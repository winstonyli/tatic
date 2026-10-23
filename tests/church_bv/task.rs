//! Process-wide memos for `driver::worker`, which runs many tasks (a sweep's children) in one process. A task's
//! configuration and outcome live in its `job::Setup`; every process-wide mutable static in church_bv is a pure memo, whose
//! value depends only on its key (configuration included), kept across tasks: a `SharedMemo`, or one of the few on
//! `job::hidden_state_is_classified`'s list, which holds every static to that rule (docs/tier-cycle.md, "A persistent
//! worker").

use std::sync::Mutex;

/// A pure memo shared by a process's threads and kept across tasks: each value must depend only on its key, configuration
/// included. `hidden_state_is_classified` takes that on trust, so each static of this type says why at its declaration.
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
    /// `key`'s value, if built: with `insert`, for a value built unlocked; `insert` says whether the key was new (two
    /// threads may build the same value, and only one inserts it first).
    pub fn get(&self, key: &K) -> Option<V>
    where
        V: Clone,
    {
        self.lock().as_ref()?.get(key).cloned()
    }
    pub fn insert(&self, key: K, v: V) -> bool {
        self.lock().get_or_insert_with(Default::default).insert(key, v).is_none()
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
    assert!(m.insert(3, vec![3]), "a new key");
    assert!(!m.insert(3, vec![3]), "a key already built");
    assert_eq!(m.with(3, || build(3), |v| v.clone()), vec![3]);
    assert_eq!(builds.get(), 1);
}
