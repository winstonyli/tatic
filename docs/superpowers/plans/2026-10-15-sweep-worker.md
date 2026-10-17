---
status: done
---

# Sweep Worker Implementation Plan

> **For agentic workers:** execute inline (superpowers:executing-plans). Each task consumes the one before it, so there
> is nothing to parallelize. Run one Sonnet review of the whole branch at the end. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Run the sweep's children as tasks of one persistent worker process, with outputs identical to the per-process
sweep's.

**Architecture:**

- Process-wide state is either a pure memo, kept across tasks, or task state. Task state is a `PerTask`/`PerTaskArc`
  value, rebuilt at its first read in each task.
- A source-scanning test enforces that split.
- The worker is an ignored test that reads tasks from stdin. It runs each task on a fresh thread, with the task's
  environment overlaid on its own and its stdout and stderr pointed at the task's log.
- The driver's `Worker` replaces `child()`.

**Tech Stack:** Rust 2024 (nightly 1.100), the church_bv test crate (tests/church_bv), Git Bash and PowerShell scripts in
docs/runs/2026-10-12/scripts.

**Spec:** docs/superpowers/specs/2026-10-15-sweep-worker-design.md

## Global Constraints

- No new dependencies. Stdio redirection uses `extern` declarations (`kernel32` `GetStdHandle`/`SetStdHandle` on Windows;
  libc `dup`/`dup2`/`close` elsewhere).
- Outputs must be identical to the base commit's on salts 1 and 2. Check with `docs/runs/2026-10-12/scripts/hc_seq.sh` and
  then `gate_cmp.sh`. The only tolerated difference is an "order only" one in `lib_sbo3/mine_ref.log` (the
  `LEMMA_CACHE starts empty` line).
- **Builds and tests:**
  - Build and test with `cmd //c start "" //b //belownormal //affinity FFF //wait cargo test --release -j 8 --test church_bv ...`
    from Git Bash.
  - Run all tests with `-- --test-threads 8`.
- **Python:** never let python read stdin. Write a script to a file and run `python -P f.py < /dev/null`.
- **Waiting:** no fixed sleeps. Wait with polling loops that have a deadline.
- **Timing:**
  - Time only with `hc_rounds.ps1`.
  - Report the CPU load and Defender's `RealTimeProtectionEnabled` with every timing, and never change Defender.
- **Base commit:** 38c4e3d (branch `shared-tree-encs`, with `TREE_ENCS` process-wide). Work on a new branch `sweep-worker`
  from it.
- **Commits:** use `@'...'@ | Out-File -Encoding ascii "$env:TEMP\msg.txt"; git commit -q -F ...`. End every message with
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. Check `git diff --cached --stat` first.
- **Files to leave alone:** the untracked `tests/ring_spike.rs` and `tests/ring_loop_spike.rs`.

## Review Focus

1. **A task panics.** The driver gets `false`, the panic message is in that task's log, and the next task runs in a fresh
   worker. Pinned in `worker_runs_tasks`, step 3 of its sequence.
2. **A task's log cannot be created** (its directory is missing). The driver gets `false`, nothing hangs, and the next task
   runs. Pinned in `worker_runs_tasks`, step 6.
3. **An environment value containing `=`.** It arrives whole, split at the first `=`. Pinned in `worker_runs_tasks`, step 1.
4. **Two tasks that disagree on a process-start variable** (`RUST_BACKTRACE`). The second gets a respawned worker; two
   that agree share one. Pinned in `worker_runs_tasks`, steps 7 to 9.
5. **The driver panics mid-sweep** (a mine's `assert!`). `Worker`'s `Drop` closes the worker's stdin and waits, so no
   worker process survives.
   - No automated test: it would need a failing mine.
   - The reviewer checks that `Drop` is the only owner of the process, and that `Worker` lives in `sweep`'s and
     `loop_stream`'s frames.

---

### Task 1: `PerTask` and `PerTaskArc`

**Files:**
- Create: `tests/church_bv/task.rs`
- Modify: `tests/church_bv/main.rs` (add `mod task;` after `mod search;`)

**Interfaces:**
- Produces:
  - `crate::task::begin(env: Vec<(String, String)>)`.
  - `crate::task::task_env() -> Vec<(String, String)>`.
  - `crate::task::PerTask<T>`: `const fn new()`, `get(&self, init: impl FnOnce() -> T) -> &'static T`. No public
    `peek`: nothing needs one.
  - `crate::task::PerTaskArc<T>`: `const fn new()`, `get(&self, init: impl FnOnce() -> T) -> Arc<T>`,
    `peek(&self) -> Option<Arc<T>>`.
  - In the module, also `get_at`/`peek_at` taking an explicit epoch.

- [ ] **Step 1: Create the branch**

Run: `git switch -c sweep-worker 38c4e3d`

- [ ] **Step 2: Write `task.rs` with the tests and stub bodies**

```rust
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
        todo!()
    }
    fn get_at(&self, epoch: usize, init: impl FnOnce() -> T) -> &'static T {
        todo!()
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
        todo!()
    }
    fn get_at(&self, epoch: usize, init: impl FnOnce() -> T) -> Arc<T> {
        todo!()
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
```

- [ ] **Step 3: Add `mod task;` to main.rs and run the test to see it fail**

In `tests/church_bv/main.rs`, add `mod task;` on the line after `mod search;`.

Run: `cmd //c start "" //b //belownormal //affinity FFF //wait cargo test --release -j 8 --test church_bv task::per_task_rebuilds_per_task -- --exact 2>&1 | tail -5`

Expected: FAIL, panicked at `not yet implemented`.

- [ ] **Step 4: Implement the four bodies**

```rust
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
```

`self.cur.store(built, Release)` coerces `&mut (usize, T)` to `*mut`. Return `&built.1` after the store: the reference is
still valid, since the box is leaked.

If the borrow checker rejects using `built` after the move into `store`, write `let ptr: *mut (usize, T) = built;`,
store `ptr`, and return `unsafe { &(*ptr).1 }` with a SAFETY comment ("leaked, never freed").

```rust
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
```

- [ ] **Step 5: Run the test**

Run the same command as in Step 3. Expected: `test result: ok. 1 passed`.

- [ ] **Step 6: Run the whole suite**

Run: `cmd //c start "" //b //belownormal //affinity FFF //wait cargo test --release -j 8 --test church_bv -- --test-threads 8 2>&1 | grep -E "test result|FAILED|panicked"`

Expected: `ok. 85 passed`. Unused-item warnings for `begin`, `task_env` and `PerTaskArc::peek` are fine until Task 2 and Task 3 use
them; do not add `#[allow]`.

- [ ] **Step 7: Commit**

```bash
git add tests/church_bv/task.rs tests/church_bv/main.rs && git diff --cached --stat
```

Message: `church_bv: PerTask and PerTaskArc, state rebuilt per worker task`. In the body, one line saying it is unused
until the next commits.

---

### Task 2: Classify every process-wide static

**Files:**
- Modify: `tests/church_bv/rewrite.rs`: `ENV` ~189-214, `ablated` ~746, `RuleTable::new` ~1156, `rule_set` ~1237,
  `fixed_rules` ~1254, `TRACE_RULES`/`RULE_HITS`/`RULE_CONFLICTS` ~1827-1836, uses ~1905, ~1911, ~1919.
- Modify: `tests/church_bv/machine.rs`:
  - `LEMMA_HITS` ~236, and its uses ~479 and ~1078.
  - `PROF` ~237, and its uses ~390, ~399, ~1077.
- Modify: `tests/church_bv/lemma_cache.rs` ~86-175.
- Modify: `tests/church_bv/search.rs`:
  - Delete the `load_exe_env();` line (~446).
  - `RULE_HITS` use ~92, `RULE_CONFLICTS` uses ~1178, ~1180, ~2020, `TRACE_RULES` ~1947.
- Modify: `tests/church_bv/task.rs` (add `task_state_is_classified`).

**Interfaces:**
- Consumes: `PerTask`, `PerTaskArc` and `task_env` from Task 1.
- Produces:
  - `env_var` and `env_or` read the current task's environment.
  - `load_exe_env` no longer exists.
  - `lemma_cache::process() -> std::sync::Arc<Option<Process>>`.

- [ ] **Step 1: Write the classification test, failing**

Append to `task.rs`:

```rust
/// The name of the process-wide mutable static declared on `line`, if any: `static mut`, or a static whose type mentions a
/// lock, a once-cell or an atomic. Thread-locals in church_bv hold `Cell`s and `RefCell`s, so they are not flagged (a lock in
/// a thread-local would be, falsely). It cannot see interior mutability behind a struct's name (`static X: Counters`):
/// no church_bv static is one.
fn flagged(line: &str) -> Option<&str> {
    let t = line.trim_start();
    let rest = ["pub(crate) static ", "pub static ", "static "].iter().find_map(|p| t.strip_prefix(p))?;
    let (is_mut, rest) = match rest.strip_prefix("mut ") {
        Some(r) => (true, r),
        None => (false, rest),
    };
    let (name, ty) = rest.split_once(':')?;
    let mutable = is_mut || ["Mutex", "RwLock", "Once", "LazyLock", "Atomic"].iter().any(|m| ty.contains(m));
    (mutable && !ty.contains("PerTask")).then_some(name.trim())
}

/// Every process-wide mutable static in church_bv is task state (`PerTask`, `PerTaskArc`) or a pure memo on this list,
/// so a `driver::worker` task never sees another task's configuration or counters.
#[test]
fn task_state_is_classified() {
    const PURE: [(&str, &str, &str); 9] = [
        ("rewrite.rs", "TABLE", "the term table: interning is pure"),
        ("rewrite.rs", "SCREENS", "values on fixed pseudo-random inputs, keyed by width and variable count"),
        ("rewrite.rs", "TREE_CANDS", "keyed by width, variable count and nops()"),
        ("rewrite.rs", "CACHE", "promoted_rules parses a constant table"),
        ("machine.rs", "TREE_ENCS", "pure in its key; carry_cap() is a screen before the lookup"),
        ("search.rs", "MEMO", "pool3_sequence, keyed by every variable it reads (the driver's)"),
        ("lemma_cache.rs", "ID", "the running exe's identity"),
        ("task.rs", "TASK", "the task machinery"),
        ("task.rs", "TASK_ENV", "the task machinery"),
    ];
    assert_eq!(flagged("    static X: std::sync::OnceLock<u8> = std::sync::OnceLock::new();"), Some("X"));
    assert_eq!(flagged("pub static Y: [std::sync::atomic::AtomicU64; 3] = x;"), Some("Y"));
    assert_eq!(flagged("static mut Z: u8 = 0;"), Some("Z"));
    assert_eq!(flagged("static W: PerTask<std::sync::Mutex<u8>> = PerTask::new();"), None);
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
```

The test file must not itself contain a line that starts with `static ` and names a lock. The `flagged` sample strings sit
inside string literals that start with `assert_eq!`, so they are safe.

Run: `cmd //c start "" //b //belownormal //affinity FFF //wait cargo test --release -j 8 --test church_bv task::task_state_is_classified -- --exact 2>&1 | grep -E "panicked|statics|test result"`

Expected: FAIL. The list names ENV, SET (twice), FIXED, RULES, TRACE_RULES, RULE_HITS, RULE_CONFLICTS, LEMMA_HITS, PROF,
PROCESS, RECORDED, HITS, BUILT, SKIPPED and R. `ID` does not exist yet, so nothing in lemma_cache.rs is called `ID`.

- [ ] **Step 2: The environment (rewrite.rs)**

Replace the `ENV` static, `env_var` and `load_exe_env` (the block from the `ENV` doc comment through the end of
`load_exe_env`) with:

```rust
/// The task's environment, taken whole at its first `env_var` (names upper-cased on Windows, where they ignore case; values
/// that are not Unicode left out). Reading a variable per call cost a sweep 4.3% of its samples, mostly `nops` in `tree_step`
/// (docs/tier-cycle.md, "The environment read once per process"). Per task (`task::PerTask`): a `driver::worker` task sees
/// the worker's environment with the task's pairs over it.
static ENV: crate::task::PerTask<hashbrown::HashMap<String, String>> = crate::task::PerTask::new();

fn env_name(k: &str) -> std::borrow::Cow<'_, str> {
    if cfg!(windows) && k.bytes().any(|b| b.is_ascii_lowercase()) { k.to_ascii_uppercase().into() } else { k.into() }
}

/// The process's environment; then `<exe>.env` (lines `KEY=VALUE`) for the names it does not set, so a profiler launcher that
/// cannot pass env (the elevated Samply task) runs the same configuration; then the task's pairs (`task::begin`).
fn env_snapshot() -> hashbrown::HashMap<String, String> {
    let mut env: hashbrown::HashMap<String, String> =
        std::env::vars_os().filter_map(|(k, v)| Some((env_name(k.to_str()?).into_owned(), v.into_string().ok()?))).collect();
    if let Ok(text) = std::env::current_exe().map(|mut p| { p.as_mut_os_string().push(".env"); p }).and_then(std::fs::read_to_string) {
        for (k, v) in text.lines().filter_map(|l| l.split_once('=')) {
            env.entry(env_name(k.trim()).into_owned()).or_insert_with(|| v.trim().to_string());
        }
    }
    for (k, v) in crate::task::task_env() {
        env.insert(env_name(&k).into_owned(), v);
    }
    env
}

/// The environment variable `k` in this task's snapshot (`ENV`), or `None` when unset: every church_bv read goes through
/// this, so a variable set after the task's first read is not seen.
pub fn env_var(k: &str) -> Option<&'static str> {
    ENV.get(env_snapshot).get(&*env_name(k)).map(String::as_str)
}
```

In search.rs, delete the `load_exe_env();` line at the top of `rule_miner`.

- [ ] **Step 3: Configuration-derived values (rewrite.rs)**

Make each change exactly as follows:

- `ablated`:
  `static SET: crate::task::PerTask<Vec<String>> = crate::task::PerTask::new();` and `SET.get(|| ...)` (same closure).
  Change the doc's "Read once per process" to "Read once per task".
- `RuleTable::new`:
  `static FIXED: crate::task::PerTask<Vec<TableRule>> = crate::task::PerTask::new();` and `FIXED.get(|| ...)`.
- `rule_set`: `static SET: crate::task::PerTask<Vec<(Term, Term)>> = crate::task::PerTask::new();` and `SET.get(|| { ... })`.
- `fixed_rules`: `static RULES: crate::task::PerTask<Vec<Rule>> = crate::task::PerTask::new();` and
  `RULES.get(build_fixed_rules)`. Its doc says "Built once per task".
- `TRACE_RULES`:
  `pub static TRACE_RULES: crate::task::PerTask<std::sync::atomic::AtomicBool> = crate::task::PerTask::new();`. Its uses
  become `TRACE_RULES.get(Default::default).load(...)` and, in search.rs, `TRACE_RULES.get(Default::default).store(...)`.
- `RULE_HITS`:
  `pub static RULE_HITS: crate::task::PerTask<std::sync::Mutex<Vec<(&'static str, u64)>>> = crate::task::PerTask::new();`.
  Its uses become `RULE_HITS.get(Default::default).lock()`, in rewrite.rs ~1919 and search.rs ~92.
- `RULE_CONFLICTS`:
  `pub static RULE_CONFLICTS: crate::task::PerTask<std::sync::Mutex<Option<hashbrown::HashMap<Pref, u64>>>> = crate::task::PerTask::new();`.
  Every `RULE_CONFLICTS.lock()` becomes `RULE_CONFLICTS.get(Default::default).lock()`: rewrite.rs ~1836 and ~1905,
  search.rs ~1178, ~1180 and ~2020.

- [ ] **Step 4: machine.rs counters**

- `LEMMA_HITS` becomes `pub static LEMMA_HITS: crate::task::PerTask<std::sync::atomic::AtomicU64> = crate::task::PerTask::new();`.
  Its uses become `LEMMA_HITS.get(Default::default).fetch_add(...)` (~479) and `LEMMA_HITS.get(Default::default).load(...)`
  (~1078, in the `LTMINER time:` line). Check with `grep -n LEMMA_HITS tests/church_bv/*.rs` that there are no others.
- `PROF` becomes
  `pub static PROF: crate::task::PerTask<[std::sync::atomic::AtomicU64; 3]> = crate::task::PerTask::new();`.
- Its uses become `PROF.get(Default::default)[i].fetch_add(...)` (two sites) and
  `PROF.get(Default::default)[i].load(...)` (one site).

- [ ] **Step 5: lemma_cache.rs**

- `OnceLock` and `Mutex` are already imported (lemma_cache.rs:11); write `std::sync::Arc` in full where it appears.
- `exe_identity` becomes:

```rust
/// A hash of this exe's bytes: the build that wrote a file. Hashed once per process (the exe does not change while it runs).
fn exe_identity() -> u64 {
    static ID: OnceLock<u64> = OnceLock::new();
    *ID.get_or_init(|| {
        use std::hash::{Hash, Hasher};
        let bytes = std::fs::read(std::env::current_exe().unwrap()).expect("read the running exe");
        let mut h = std::collections::hash_map::DefaultHasher::new();
        bytes.hash(&mut h);
        h.finish()
    })
}
```

- The statics and `process`:

```rust
/// This task's cache (the file is read again in each `driver::worker` task, which sees the earlier tasks' saves) and
/// counters.
static PROCESS: crate::task::PerTaskArc<Option<Process>> = crate::task::PerTaskArc::new();
static RECORDED: crate::task::PerTask<Mutex<Vec<(String, Vec<u8>)>>> = crate::task::PerTask::new();
static HITS: crate::task::PerTask<AtomicU64> = crate::task::PerTask::new();
static BUILT: crate::task::PerTask<AtomicU64> = crate::task::PerTask::new();
static SKIPPED: crate::task::PerTask<AtomicU64> = crate::task::PerTask::new();

/// This task's cache, read at first use; `None` inside without `LEMMA_CACHE`.
fn process() -> std::sync::Arc<Option<Process>> {
    PROCESS.get(|| {
        let path = PathBuf::from(env_var("LEMMA_CACHE")?);
        let identity = exe_identity();
        let cache = Cache::load(&path, identity);
        if let Some(why) = &cache.why_empty {
            eprintln!("LEMMA_CACHE starts empty: {why}");
        }
        Some(Process { path, identity, cache })
    })
}
```

- `recheck`: `static R: crate::task::PerTask<bool> = crate::task::PerTask::new();` and `*R.get(|| ...)`.
- `lookup`: `let p = process(); let b = (*p).as_ref()?.cache.get(key)?;`. Then `HITS.get(Default::default).fetch_add(1, Relaxed)`.
- `record`: `if process().is_none() { return; }` (auto-deref on the `Arc`). Then use
  `BUILT.get(Default::default)`, `RECORDED.get(Default::default).lock()` and `SKIPPED.get(Default::default)`.
- `Save::drop`: `let Some(arc) = PROCESS.peek() else { return }; let Some(p) = &*arc else { return };`. Then
  `RECORDED.get(Default::default)` and the three counters via `.get(Default::default).load(Relaxed)`. Keep the comment "a
  process that never looked anything up has nothing to add", with "process" changed to "task".

- [ ] **Step 6: Run the classification test, then everything**

Run the Step 1 command. Expected: PASS.

Mutation check: temporarily add the line `static PROBE: std::sync::Mutex<u8> = std::sync::Mutex::new(0); // PROBE` to the
end of rewrite.rs. Run the test: expected FAIL naming `rewrite.rs:<line> PROBE`. Then run
`sed -i '/\/\/ PROBE$/d' tests/church_bv/rewrite.rs` and confirm with `grep -c PROBE tests/church_bv/rewrite.rs` (0).

Run the whole suite (the Task 1 Step 6 command). Expected: `ok. 86 passed`.

- [ ] **Step 7: Gate. A one-task process must behave exactly as before.**

```bash
K="$TEMP/kk"; mkdir -p "$K/pt" && cp "$(ls -t target/release/build/tatic/*/out/church_bv-*.exe | head -1)" "$K/pt/new.exe" && cp "$K/te/new.exe" "$K/pt/old.exe"
bash docs/runs/2026-10-12/scripts/hc_seq.sh pt "$K/pt/old.exe" "$K/pt/new.exe" && bash docs/runs/2026-10-12/scripts/gate_cmp.sh pt
```

If cargo's hash directory changed, find the exe with `ls -t target/release/build/tatic/*/out/church_bv-*.exe | head -1`.
`$K/te/new.exe` is 38c4e3d's build.

Expected: "same file list (416 files)" on both salts and no DIFF lines. The one exception is a possible
`lib_sbo3/mine_ref.log` DIFF. Check it with `diff <(sort ...) <(sort ...)` after normalizing timings: it may only differ
in order.

- [ ] **Step 8: Commit**

Message: `church_bv: process-wide task state is PerTask; the source check holds every static to it`. The body lists:

- The statics converted.
- `LEMMA_HITS` made per-task like `PROF`.
- `load_exe_env` folded into the environment snapshot.
- The exe identity hashed once per process.
- The gate result.

---

### Task 3: The worker and the driver's `Worker`

**Files:**
- Modify: `tests/church_bv/driver.rs`:
  - The module doc, lines 1-3.
  - `child` (~96) is replaced.
  - `machine_state` (~108) and `run_loop` (~129, its `mine` and `serve` closures).
  - `loop_stream` (~217) and `sweep` (~238, ~258, ~339).
  - New items: `stdio`, `worker`, `task_fn`, `env_echo`, `Worker`, `WorkerProc`, `process_start` and `worker_runs_tasks`.

**Interfaces:**
- Consumes: `crate::task::begin` from Task 1, and `env_var` from Task 2.
- Produces: `Worker::new()`, `Worker::run(&self, name: &str, env: &[(String, String)], log: &Path) -> bool`, and `Drop`.

- [ ] **Step 1: Write `env_echo` and `worker_runs_tasks` (failing: `Worker` does not exist)**

Add after `machine_state` in driver.rs:

```rust
/// Prints `env_var(k)` for each name in `ECHO` (a comma list) and a nonce unique to this process; panics when
/// `ECHO_PANIC=1`. A task for `worker_runs_tasks`.
#[test]
#[ignore]
fn env_echo() {
    static NONCE: std::sync::OnceLock<u128> = std::sync::OnceLock::new();
    let nonce = NONCE.get_or_init(|| std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos());
    for k in env_var("ECHO").unwrap_or("").split(',').filter(|k| !k.is_empty()) {
        println!("ECHO {k}={}", env_var(k).unwrap_or("<unset>"));
    }
    println!("ECHO nonce={nonce}");
    assert!(env_var("ECHO_PANIC") != Some("1"), "env_echo panicked on request");
}

/// A worker runs each task with its own environment and log, leaks no variable from one task to the next, starts afresh
/// after a failed task, and is replaced when a task's process-start variables differ. Starts processes:
/// `cargo test --release --test church_bv driver::worker_runs_tasks -- --exact --ignored --nocapture`.
#[test]
#[ignore]
fn worker_runs_tasks() {
    let dir = std::env::temp_dir().join(format!("worker_runs_tasks_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let kv = |k: &str, v: &str| (k.to_string(), v.to_string());
    let log = |i: usize| dir.join(format!("{i}.log"));
    let w = Worker::new();
    let ok = [
        w.run("driver::env_echo", &[kv("ECHO", "A,B,C"), kv("A", "1"), kv("C", "x=y")], &log(1)),
        w.run("driver::env_echo", &[kv("ECHO", "A,B"), kv("B", "2")], &log(2)),
        w.run("driver::env_echo", &[kv("ECHO_PANIC", "1")], &log(3)),
        w.run("driver::env_echo", &[kv("ECHO", "A")], &log(4)),
        w.run("driver::no_such_task", &[], &log(5)),
        w.run("driver::env_echo", &[], &dir.join("missing").join("6.log")),
        w.run("driver::env_echo", &[kv("RUST_BACKTRACE", "0")], &log(7)),
        w.run("driver::env_echo", &[kv("RUST_BACKTRACE", "0")], &log(8)),
        w.run("driver::env_echo", &[], &log(9)),
    ];
    assert_eq!(ok, [true, true, false, true, false, false, true, true, true]);
    let text = |i: usize| std::fs::read_to_string(log(i)).unwrap();
    let echoes = |i: usize| text(i).lines().filter(|l| !l.starts_with("ECHO nonce=")).map(String::from).collect::<Vec<_>>();
    let nonce = |i: usize| text(i).lines().find_map(|l| l.strip_prefix("ECHO nonce=").map(String::from)).unwrap();
    assert_eq!(echoes(1), ["ECHO A=1", "ECHO B=<unset>", "ECHO C=x=y"]);
    assert_eq!(echoes(2), ["ECHO A=<unset>", "ECHO B=2"], "no variable leaks from task 1");
    assert!(text(3).contains("env_echo panicked on request"), "3.log: {}", text(3));
    assert!(text(5).contains("no task driver::no_such_task"), "5.log: {}", text(5));
    assert_eq!(nonce(1), nonce(2), "tasks 1 and 2 ran in one worker");
    assert_ne!(nonce(2), nonce(4), "a fresh worker after the panic");
    assert_eq!(nonce(7), nonce(8), "tasks with the same process-start variables share a worker");
    assert_ne!(nonce(8), nonce(9), "a different RUST_BACKTRACE gets a fresh worker");
    for i in [1, 2, 4, 7, 8, 9] {
        assert!(text(i).lines().all(|l| l.starts_with("ECHO ")), "{i}.log holds only its task's lines: {}", text(i));
    }
    drop(w);
    std::fs::remove_dir_all(&dir).unwrap();
}
```

`NONCE` is process-wide on purpose: it identifies the process. In `task.rs`, change `PURE`'s length from 9 to 10 and add the
entry `("driver.rs", "NONCE", "env_echo's per-process nonce, process-wide on purpose")`.

Run: `cmd //c start "" //b //belownormal //affinity FFF //wait cargo test --release -j 8 --test church_bv --no-run 2>&1 | grep -E "^error" | head -3`

Expected: `error[E0433]` or `E0425`, failed to resolve `Worker`.

- [ ] **Step 2: Stdio redirection, the worker test and the task table**

Add to driver.rs, after `use std::process::Command;`, the import `use std::io::{BufRead, BufReader};`. Then add:

```rust
/// The process's stdout and stderr pointed at one file, for a task's log (`worker`): one handle (one fd) for both, so they
/// share the file offset as a child's `try_clone`d handles do. std looks the handle up on every write (checked by a probe,
/// docs/superpowers/specs/2026-10-15-sweep-worker-design.md), so `println!` follows it.
#[cfg(windows)]
mod stdio {
    use std::ffi::c_void;
    use std::os::windows::io::AsRawHandle;
    unsafe extern "system" {
        fn GetStdHandle(which: u32) -> *mut c_void;
        fn SetStdHandle(which: u32, handle: *mut c_void) -> i32;
    }
    const OUT: u32 = -11i32 as u32;
    const ERR: u32 = -12i32 as u32;
    pub struct Saved([*mut c_void; 2]);
    pub fn redirect(f: &std::fs::File) -> Saved {
        // SAFETY: plain Win32 calls; `f` outlives the redirection (`restore` runs before it drops)
        unsafe {
            let saved = Saved([GetStdHandle(OUT), GetStdHandle(ERR)]);
            SetStdHandle(OUT, f.as_raw_handle());
            SetStdHandle(ERR, f.as_raw_handle());
            saved
        }
    }
    pub fn restore(s: Saved) {
        // SAFETY: the handles `redirect` saved, still open
        unsafe {
            SetStdHandle(OUT, s.0[0]);
            SetStdHandle(ERR, s.0[1]);
        }
    }
}
#[cfg(unix)]
mod stdio {
    use std::os::fd::AsRawFd;
    unsafe extern "C" {
        fn dup(fd: i32) -> i32;
        fn dup2(from: i32, to: i32) -> i32;
        fn close(fd: i32) -> i32;
    }
    pub struct Saved([i32; 2]);
    pub fn redirect(f: &std::fs::File) -> Saved {
        // SAFETY: plain libc calls on fds this process owns
        unsafe {
            let saved = Saved([dup(1), dup(2)]);
            dup2(f.as_raw_fd(), 1);
            dup2(f.as_raw_fd(), 2);
            saved
        }
    }
    pub fn restore(s: Saved) {
        // SAFETY: the fds `redirect` duplicated, closed once here
        unsafe {
            dup2(s.0[0], 1);
            dup2(s.0[1], 2);
            close(s.0[0]);
            close(s.0[1]);
        }
    }
}

/// The tests a worker runs as tasks.
fn task_fn(name: &str) -> Option<fn()> {
    Some(match name {
        "search::rule_miner" => crate::search::rule_miner,
        "search::rule_set_kernel_check" => crate::search::rule_set_kernel_check,
        "machine::machine_state_line" => crate::machine::machine_state_line,
        "driver::env_echo" => env_echo,
        _ => return None,
    })
}

/// A sweep's children as tasks of one process (`Worker` starts it, with `TATIC_WORKER=1`; it returns at once otherwise).
/// Reads `<test>\t<log>\t<KEY>=<VALUE>...` lines; runs each test on a fresh thread (fresh thread-locals) with the task's
/// pairs over this process's environment (`task::begin`) and its stdout and stderr in the log; answers `WORKER ok` or
/// `WORKER fail` on a line of its own, and exits after a failure (a panic can leave a lock poisoned) or at EOF. A task that
/// starts a process must give it a null stdin, as `Command::output` does: this stdin is the task pipe.
#[test]
#[ignore]
fn worker() {
    if std::env::var_os("TATIC_WORKER").is_none() {
        return;
    }
    for line in std::io::stdin().lines() {
        let line = line.expect("the task pipe");
        let mut fields = line.split('\t');
        let (name, log) = (fields.next().unwrap_or("").to_string(), fields.next().unwrap_or("").to_string());
        let env = fields.filter_map(|f| f.split_once('=')).map(|(k, v)| (k.to_string(), v.to_string())).collect();
        crate::task::begin(env);
        let ok = match std::fs::File::create(&log) {
            Ok(f) => {
                std::io::stdout().flush().unwrap();
                let saved = stdio::redirect(&f);
                let ok = match task_fn(&name) {
                    Some(run) => std::thread::Builder::new().name(name.clone()).spawn(run).unwrap().join().is_ok(),
                    None => {
                        eprintln!("worker: no task {name}");
                        false
                    }
                };
                std::io::stdout().flush().unwrap();
                stdio::restore(saved);
                ok
            }
            Err(e) => {
                eprintln!("worker: cannot create {log}: {e}");
                false
            }
        };
        println!("\nWORKER {}", if ok { "ok" } else { "fail" });
        if !ok {
            return;
        }
    }
}
```

- [ ] **Step 3: The driver's `Worker`, replacing `child`**

Replace `child` (its doc comment and body) with:

```rust
/// The child process that runs this driver's children as tasks (`worker`), started at the first task and again after a
/// failed one, or when a task's process-start variables (`process_start`) differ from its. Dropping it closes the worker's
/// stdin and waits for it, so no worker outlives its driver.
struct Worker {
    proc: std::sync::Mutex<Option<WorkerProc>>,
}

struct WorkerProc {
    child: std::process::Child,
    stdin: std::process::ChildStdin,
    stdout: BufReader<std::process::ChildStdout>,
    start: Vec<(String, String)>,
}

/// The pairs of `env` read when a process starts (mimalloc's options, std's `RUST_MIN_STACK` and `RUST_BACKTRACE`), the last
/// of each name winning: a worker serves only tasks that agree on them.
fn process_start(env: &[(String, String)]) -> Vec<(String, String)> {
    let start: std::collections::BTreeMap<&str, &str> =
        env.iter().filter(|(k, _)| k.starts_with("MIMALLOC_") || k.starts_with("RUST_")).map(|(k, v)| (k.as_str(), v.as_str())).collect();
    start.into_iter().map(|(k, v)| (k.to_string(), v.to_string())).collect()
}

impl Worker {
    fn new() -> Worker {
        Worker { proc: std::sync::Mutex::new(None) }
    }

    /// Runs test `name` of this exe with `env` added, output to `log`; returns whether it succeeded.
    fn run(&self, name: &str, env: &[(String, String)], log: &Path) -> bool {
        let mut slot = self.proc.lock().unwrap_or_else(|e| e.into_inner());
        let start = process_start(env);
        if slot.as_ref().is_some_and(|p| p.start != start) {
            Self::stop(slot.take().unwrap());
        }
        let p = slot.get_or_insert_with(|| Self::spawn(start));
        let fields: Vec<String> = [name.to_string(), log.display().to_string()].into_iter().chain(env.iter().map(|(k, v)| format!("{k}={v}"))).collect();
        assert!(fields.iter().all(|f| !f.contains(['\t', '\n', '\r'])), "a task field holds a tab or a newline: {fields:?}");
        let sent = writeln!(p.stdin, "{}", fields.join("\t")).and_then(|_| p.stdin.flush()).is_ok();
        // a failed task ends the worker; EOF before a reply means it died (its log is then partial, as a crashed child's)
        let ok = sent && (&mut p.stdout).lines().map_while(Result::ok).find_map(|l| l.strip_prefix("WORKER ").map(|r| r == "ok")) == Some(true);
        if !ok {
            Self::stop(slot.take().unwrap());
        }
        ok
    }

    fn spawn(start: Vec<(String, String)>) -> WorkerProc {
        let mut child = Command::new(std::env::current_exe().unwrap())
            .args(["driver::worker", "--exact", "--ignored", "--nocapture"])
            .envs(start.iter().cloned())
            .env("TATIC_WORKER", "1")
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .expect("start the worker");
        let (stdin, stdout) = (child.stdin.take().unwrap(), BufReader::new(child.stdout.take().unwrap()));
        WorkerProc { child, stdin, stdout, start }
    }

    /// Closes the worker's stdin, reads its stdout to EOF (libtest's closing lines must not meet a closed pipe) and waits.
    fn stop(p: WorkerProc) {
        let WorkerProc { mut child, stdin, mut stdout, .. } = p;
        drop(stdin);
        let _ = std::io::copy(&mut stdout, &mut std::io::sink());
        let _ = child.wait();
    }
}

impl Drop for Worker {
    fn drop(&mut self) {
        if let Some(p) = self.proc.get_mut().unwrap_or_else(|e| e.into_inner()).take() {
            Self::stop(p);
        }
    }
}
```

- [ ] **Step 4: Route the driver through the `Worker`**

1. **`machine_state`** becomes:

```rust
/// A machine-state line on stderr (about 6 s), taken by a worker task with the children's `env` so its `pages=` is theirs,
/// logged to `<out>/machine_state_<when>.log`; `MACHINE_STATE=0` skips it, in a loop or a sweep.
fn machine_state(when: &str, env: &[(String, String)], worker: &Worker, out: &Path) {
    if env_or("MACHINE_STATE", 1usize) == 0 {
        return;
    }
    std::fs::create_dir_all(out).unwrap();
    let log = out.join(format!("machine_state_{when}.log"));
    worker.run("machine::machine_state_line", env, &log);
    let text = std::fs::read_to_string(&log).unwrap_or_default();
    eprintln!("machine at {when}: {}", text.lines().find(|l| l.contains("machine state:")).unwrap_or(""));
}
```

2. **`run_loop`:**
   - Its signature becomes `fn run_loop(cfg: &LoopCfg, lemmas: &Path, worker: &Worker) -> Summary`.
   - In `mine`: `assert!(worker.run("search::rule_miner", &env, &log), ...)`, keeping the message.
   - In `serve`: `worker.run("search::rule_set_kernel_check", &env, &log);`.
3. **`loop_stream`:**
   - Add `let worker = Worker::new();` as its first line.
   - Its calls become `machine_state("start", &cfg.env, &worker, &cfg.out)`, `run_loop(&cfg, &lemmas, &worker)` and
     `machine_state("end", &cfg.env, &worker, &cfg.out)`.
4. **`sweep`:**
   - Add `let worker = Worker::new();` just before the first `machine_state("start", ...)`.
   - Every `machine_state(x, &env)` becomes `machine_state(x, &env, &worker, &out)`.
   - Every `run_loop(&cfg, &lemmas)` becomes `run_loop(&cfg, &lemmas, &worker)`. There are three: the mines, pooled_prefs
     and the loops.
5. **Module doc, lines 2-3** (the sentence wraps at `//! `, so match across the line break): replace "run as child processes of this exe, so each keeps its own thread-locals and env-read
   config." with "run as tasks of one worker process of this exe (`worker`, `Worker`): each task gets fresh thread-locals,
   its own environment and its own log, while the pure memos carry over (`task.rs`)."
6. **Check:** `grep -n "child(\|Command::new" tests/church_bv/driver.rs` shows only `Worker::spawn`'s `Command::new`.

- [ ] **Step 5: Build, run the worker test, run the suite**

```bash
cmd //c start "" //b //belownormal //affinity FFF //wait cargo test --release -j 8 --test church_bv driver::worker_runs_tasks -- --exact --ignored --nocapture 2>&1 | grep -E "test result|panicked|assert" | head
```

Expected: `ok. 1 passed`.

Then run the suite (the Task 1 Step 6 command). Expected: `ok. 86 passed` and `driver::worker` among the ignored tests.

Then run the `--ignored` guard check:
`"$(ls -t target/release/build/tatic/*/out/church_bv-*.exe | head -1)" driver::worker --exact --ignored < /dev/null`.
Expected: it returns at once with `1 passed`.

Check for leftovers in PowerShell: `(Get-Process church_bv* -EA 0 | ? Path -like '*\tatic\target\*').Count` must print
`0`. Other sessions run church_bv exes from their own trees, so count only this tree's.

`cargo test -- --ignored` now also runs `env_echo` (harmless) and `worker_runs_tasks`, which starts worker processes and
cleans them up.

- [ ] **Step 6: Commit**

Message: `church_bv: the driver runs its children as tasks of one worker process`. The body covers:

- The protocol.
- The per-task thread.
- The redirection.
- Respawn on failure and on process-start variables.
- `child` deleted.
- That the gate result follows in the next commit.

---

### Task 4: Gate, memory, timing, docs

**Files:**
- Modify: `docs/runs/2026-10-12/scripts/gate_cmp.sh`
- Modify: `docs/tier-cycle.md` (new entry after "Survey: long-lived sweep workers...", plus a line in its options list)
- Modify: `docs/runs/2026-10-12/README.md` (rows appended)

- [ ] **Step 1: `gate_cmp.sh` drops libtest's lines, normalizes every tsv's seconds, and labels order-only differences**

Replace the file with:

```bash
# gate_cmp.sh <tag>: compare $TEMP/kk/<tag>_old_<s> with <tag>_new_<s> for salts 1 and 2, with timings and libtest's harness
# lines normalized away; a difference that sorting both files removes is reported as "(order only)"
k=$(cygpath -u "$TEMP")/kk; tag=$1
norm() { case "$(basename $1)" in
  cold.tsv|own.tsv|pooled.tsv) cut -f1-6,8- "$1";; mines.tsv|pooled_prefs.tsv) cut -f1,3- "$1";; m.tsv) cut -f1-4,6- "$1";;
  *.txt|*.log) sed -E "s/[0-9]+(\.[0-9]+)?(s|ms|µs)\b/T/g; s/${tag}_(old|new)/RUN/g; s/[0-9]+ filtered out/N filtered out/; /^running [0-9]+ tests?$/d; /^test .* \.\.\. (ok|FAILED|ignored)$/d; /^test result: /d; /^$/d" "$1";;
  *) cat "$1";; esac; }
for s in 1 2; do o=$k/${tag}_old_$s; n=$k/${tag}_new_$s
  diff <(cd $o && find . -type f | sort) <(cd $n && find . -type f | sort) && echo "salt $s: same file list ($(cd $o && find . -type f | wc -l) files)"
  (cd $o && find . -type f) | while read f; do cmp -s <(norm "$o/$f") <(norm "$n/$f") && continue
    cmp -s <(norm "$o/$f" | sort) <(norm "$n/$f" | sort) && echo "DIFF salt $s $f (order only)" || echo "DIFF salt $s $f"; done
done; echo cmp done
```

Check that the new normalization is no looser than needed: rerun `bash docs/runs/2026-10-12/scripts/gate_cmp.sh pt` on
Task 2's outputs. Expected: the same result as before.

- [ ] **Step 2: Gate the worker against 38c4e3d**

```bash
K="$TEMP/kk"; mkdir -p "$K/wk" && cp "$(ls -t target/release/build/tatic/*/out/church_bv-*.exe | head -1)" "$K/wk/new.exe" && cp "$K/te/new.exe" "$K/wk/old.exe"
bash docs/runs/2026-10-12/scripts/hc_seq.sh wk "$K/wk/old.exe" "$K/wk/new.exe" && bash docs/runs/2026-10-12/scripts/gate_cmp.sh wk
```

Expected: 416 files on both salts, and no DIFF lines except possibly `lib_sbo3/mine_ref.log (order only)`.

Any other DIFF means a static is misclassified, or the worker changed an output. Stop and find it:

1. `diff` the two normalized files.
2. Find which task first differs.
3. Check that task's statics.

Do not loosen the gate.

Also check in PowerShell that no worker survived: `Get-Process church_bv*, new, old -EA 0 | ? Path -like '*\kk\wk\*'` shows
nothing.

Limits:
- The libtest-line normalization assumes the old children ran on more than one core, so that `test X ... ok` is a line
  of its own. With affinity FFF it is.
- A driver killed outright (rather than panicking) runs no `Drop`. Its worker then sees EOF only after its current task
  ends, and can linger for up to one task. The same goes for a killed old driver's child.

- [ ] **Step 3: Memory**

```powershell
powershell -NoProfile -File "C:\Users\Winston Li\Documents\GitHub\tatic\docs\runs\2026-10-12\scripts\sweep_job.ps1" "$env:TEMP\kk\wk\new.exe" normal 91
```

It writes to `$env:TEMP\kk\lp_sweep_normal_91`; check first that no such directory holds someone else's run. It leaves
`MACHINE_STATE` on, so that tree also holds `machine_state_start.log` and `machine_state_end.log`. That is expected, and
the gate never sees this tree.

Record `peakproc=` (the largest single process's peak commit, which is now the worker's) and every other field the script
prints.

- If `peakproc` is under 2048 MB, no cap is needed. Record the number in the docs.
- If it is over: stop and report. The spec's cap is a design change to confirm, not to improvise.

- [ ] **Step 4: Timing**

Check the load and Defender first, as in Global Constraints. If CPU is over about 25%, wait for it to drop (a polling loop
with a deadline) or report the run as contended.

Then launch:

```powershell
$s = "C:\Users\Winston Li\Documents\GitHub\tatic\docs\runs\2026-10-12\scripts\hc_rounds.ps1"; $k = "$env:TEMP\kk"; if (Test-Path "$k\hc_rounds.txt") { Remove-Item "$k\hc_rounds.txt" }; (Start-Process powershell -WindowStyle Hidden -PassThru -ArgumentList "-NoProfile -ExecutionPolicy Bypass -File `"$s`" `"$k\wk\old.exe`" `"$k\wk\new.exe`"").Id
```

Wait for `hc_rounds ALL` in `$TEMP/kk/hc_rounds.txt`:
`d=$(( $(date +%s) + 1800 )); until grep -q "hc_rounds ALL" "$TEMP/kk/hc_rounds.txt" 2>/dev/null || [ $(date +%s) -gt $d ]; do ping -n 11 127.0.0.1 > /dev/null; done`
(run it as a Monitor or a background Bash task; `ping` waits without spinning a core, which `read -t` on `/dev/zero` would). Then copy the file to `$TEMP/kk/wk/hc_rounds.txt`.

Report the median job CPU and wall time for old and new, pairs won, the load, and Defender's state.

- [ ] **Step 5: Docs**

**tier-cycle.md, new entry** after the survey entry. Title: `**A persistent worker for the sweep's children (2026-10-1x,
branch sweep-worker): identical outputs, job CPU <x>% / wall <y>%.**`. Sub-bullets, in this order:

- **Mechanism:** one paragraph, citing the spec path.
- **The classification rule and its check.**
- **What was cut:** `child` and `load_exe_env`.
- **Outputs:** the gate result.
- **Memory:** the `peakproc` result.
- **Timing:** numbers, load, Defender.
- **What remains outside own code:** "unmeasured; a profile is the next step", unless a profile was taken.

**In the survey entry's ranked options**, append to option 1: "Done: see 'A persistent worker...' below." Also note option 3
(`TREE_ENCS`) as done on `shared-tree-encs`, if that entry exists by then.

**README rows:** append with printf, one row each for `pt` (the Task 2 gate) and `wk` (the gate, memory and timing), in
the README's existing column format. Read its last five lines first to copy the format.

- [ ] **Step 6: Commit**

Commit `gate_cmp.sh`, `tier-cycle.md` and `README.md`. Message:
`Docs: the sweep worker's gate, memory and timing; gate_cmp ignores libtest lines`.
