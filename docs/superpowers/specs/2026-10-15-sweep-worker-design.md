---
status: done
---

# A persistent worker for the sweep's children (design)

Status: built in 4e5177e and 309fa77; timed in 0ba80a0 (job CPU -14.4%, wall -14.0%). Source: docs/tier-cycle.md, "Survey: long-lived sweep workers, and the work children repeat"
(option 1).

## Goal

`driver::sweep` and `driver::loop_stream` run each child (`search::rule_miner`, `search::rule_set_kernel_check`,
`machine::machine_state_line`) as a new process of the test exe. A salt-1 gate sweep runs 169 children: 108 serves and 61
mines; the survey rounded this to 170. The survey measured:

- About 16% of busy samples fall outside own code.
  - Part of it is thread start and exit, which a worker keeps: the mines still start 59 threads each.
  - The part the worker removes is process start and exit.
- An empty launch costs 7.4 ms of CPU and 23 ms of wall time. Over 169 children that is about 1.3 s of the sweep's 13.5 s
  of CPU and about 3.9 s of wall time. A quiet sweep takes about 18-19 s of wall time (the "hash-rest" and "fill-loops"
  entries).
- 96% of value-memo fills recompute a vector an earlier child already had (about 3.3% of busy).
- `exe_identity` hashes the 3.9 MB exe once in every child (1.2%).

This design replaces the per-child process with one long-lived worker process that runs the children as tasks, one after
another. Its outputs must be identical to the per-process sweep's.

**Not in scope:**

- Thread churn inside a mine: 59 threads per mine come from per-round scoped pools.
- Keeping the lemma cache in memory across tasks (parked below).
- Running tasks in parallel.

## The one rule: task state vs. pure memos

Every process-wide piece of mutable state in church_bv belongs to exactly one of two classes:

- **Pure memo.** Its value for a key depends only on the key, and the key includes everything the value reads, configuration
  included. A pure memo carries across tasks unchanged; that carry-over is the point of the worker.
  - The term table (`TABLE`).
  - `SCREENS`, `TREE_CANDS` (keyed with `nops()`), and `TREE_ENCS`.
    - `TREE_ENCS`'s one configuration read, `carry_cap()`, is a screen before the lookup.
    - It is process-wide only from branch `shared-tree-encs` (2026-10-15), which this design builds on.
  - `pool3_sequence`'s `MEMO` (keyed with every variable it reads). Only the driver uses it, since children read law files,
    so it never reaches a task.
  - `promoted_rules`' `CACHE` (parses a constant table).
  - The exe identity (new; see the lemma cache).
- **Task state.** Anything derived from configuration, and every counter or log buffer a task prints from.
  - Becomes a `PerTask<T>`: a lazily initialized value that is rebuilt the first time it is read in a new task.
  - In a process that runs a single test, `PerTask` behaves like `OnceLock`.

Thread-locals need no class. Each task runs on a fresh thread, so every thread-local, church_bv's and the kernel's
(`SPACES`, the lazy kernel's `MEMO`, ...), starts empty in every task.

- The worker `join`s the task thread, and that waits for the OS thread to exit, its TLS destructors included.
- The task's own pools are scoped. `thread::scope` returns when the closures do, so a pool thread's TLS destructors can
  still be running as the task ends. They only free memory: none prints, and none touches state another thread reads.

### `PerTask<T>` (rewrite.rs, beside `ENV`)

```rust
/// The task this process is running: 0 in a process that runs one test, bumped by `driver::worker` before each task.
static TASK: AtomicUsize = AtomicUsize::new(0);

/// A value built at its first read in each task (in a one-test process, once: `OnceLock`). Each task's value is leaked,
/// so `T` must be small (the environment snapshot, rule lists, counters, an `Arc` handle).
pub struct PerTask<T> { cur: AtomicPtr<(usize, T)>, init: Mutex<()> }

impl<T: Send + Sync + 'static> PerTask<T> {
    pub const fn new() -> Self;
    /// This task's value, built by `init` at the task's first read.
    pub fn get(&self, init: impl FnOnce() -> T) -> &'static T { self.get_at(TASK.load(Relaxed), init) /* begin runs before the task thread spawns, which orders it */ }
    /// This task's value if this task built one, without building it (`OnceLock::get`).
    // no public peek: only PerTaskArc (PROCESS, for Save::drop) needs one
    /// The value for task `epoch` (tests use this, never bumping `TASK`).
    fn get_at(&self, epoch: usize, init: impl FnOnce() -> T) -> &'static T;
}
```

- **`peek` keeps `Save::drop`'s rule.** `Save::drop` (lemma_cache.rs ~162) uses `PROCESS.get()` so that a process that
  never looked anything up loads nothing and prints nothing. It becomes `PROCESS.peek()`.
- **Large values are not leaked.** The lemma cache's `Process` holds the whole parsed file. In past runs that file reached
  about 1.8 MB (`bytes=1768518`), so 169 leaked copies would be about 0.3 GB.
  - So `PerTask` gets a second form for values too large to leak: `PerTaskArc<T>`. It is a `Mutex<Option<(usize, Arc<T>)>>`
    with the same `get` and `peek`, which return `Arc<T>` clones.
  - On the first read in a new task it replaces the old entry, so the previous task's value drops with its last `Arc`.
  - A leaked `PerTask<Arc<..>>` would not do: the leaked box keeps its `Arc` alive forever.
  - `PROCESS` becomes `PerTaskArc<Option<Process>>`, and `process()` returns the `Arc`.
  - Its lock is taken once per `lookup`. `lookup` is 2.3% of a sweep in all, so the lock costs at most a share of that;
    the timing step covers it.
  - The check accepts both forms.

- **The fast path** is one acquire load and one compare: `cur` is non-null and its epoch equals `TASK`.
- **The slow path** takes `init`'s lock, checks again, builds the value, leaks it, and stores it.
- **Recursion.** An `init` may read *other* `PerTask`s; `ENV` is the usual one. It must not read its own `PerTask`, which
  would deadlock. No current initializer does.
- **Leaking keeps `&'static`.** The existing APIs return `&'static` (`env_var -> Option<&'static str>`, `rule_set`,
  `fixed_rules`, `ablated`'s set), so no caller changes.

**What becomes `PerTask`.** Every process-wide mutable static in tests/church_bv that is not a pure memo:

| static | file | now | why task state |
|---|---|---|---|
| `ENV` | rewrite.rs ~189 | `OnceLock<HashMap>` | the task's configuration |
| `ablated`'s `SET` | rewrite.rs ~746 | `OnceLock` | from `ABLATE` |
| `RuleTable::new`'s `FIXED` | rewrite.rs ~1156 | `OnceLock` | from `RULESET` via `fixed_rules` |
| `rule_set`'s `SET` | rewrite.rs ~1237 | `OnceLock` | from `RULESET` |
| `fixed_rules`' `RULES` | rewrite.rs ~1254 | `OnceLock` | from `rule_set` |
| `TRACE_RULES` | rewrite.rs ~1827 | `AtomicBool` | set from `NF_TRACE` by one test |
| `RULE_HITS`, `RULE_CONFLICTS` | rewrite.rs ~1830 | `Mutex` | printed counters |
| `LEMMA_HITS`, `PROF` | machine.rs ~236 | atomics | printed counters |
| `PROCESS` (as `PerTaskArc`), `RECORDED`, `HITS`, `BUILT`, `SKIPPED` | lemma_cache.rs ~100 | `OnceLock`, `Mutex`, atomics | the cache file is reloaded per task; printed counters |
| `recheck`'s `R` | lemma_cache.rs ~123 | `OnceLock` | from `LEMMA_RECHECK` |

- **Counters.** A counter becomes `PerTask<AtomicU64>` (or a `Mutex`), and each use reads `X.get(Default::default)`.
- **The exe identity** moves out of `PROCESS` into its own process-wide `OnceLock<u64>`. It is a pure memo: the exe does
  not change while it runs.

**The runnable check (new test, `task_state_is_classified`).**

- **What it scans:** every `.rs` file in `tests/church_bv`, read at run time from `CARGO_MANIFEST_DIR`, so a new module
  cannot be skipped.
- **What it flags:** every `static` outside `thread_local!` blocks whose type is process-wide mutable: `Mutex`, `RwLock`,
  `OnceLock`, `OnceCell`, `LazyLock`, `Once`, `Atomic*`, or any `static mut`.
- **What passes:** a `PerTask`, or an entry on a named allowlist, each with its one-line reason. The allowlist holds the pure
  memos above and the task machinery itself (`TASK`, `TASK_ENV`, `env_echo`'s nonce). Anything else fails, so a future static has to be
  classified, or the suite fails.

- **Library statics** (src/, audited): `compile.rs`'s three failure counters and `ir_fuzz.rs`'s `ENGINE` are not reached
  from church_bv's tasks. Everything else in src/ is a thread-local.
- **The check covers tests/church_bv only.** A new src static reached from a task would not be caught. That gap is stated
  here, and the gate still catches any such static that changes an output.

### The environment

- `ENV` becomes `PerTask<HashMap<String, String>>`. Its initializer takes three layers, later winning:
  1. The process environment (`std::env::vars_os`, names through `env_name`).
  2. `<exe>.env` for names not set by the first layer (see `load_exe_env` below).
  3. The current task's pairs (`TASK_ENV: Mutex<Vec<(String, String)>>`, set by the worker, names through `env_name`).
- In a one-test process, `TASK_ENV` is empty, so the snapshot is today's.
- **`load_exe_env` is deleted**, and with it its `unsafe set_var` and its "after the environment was read" assert.
  - Its job (a profiler launcher that cannot pass environment variables) becomes the second layer.
  - Only `rule_miner` called it. Folding it into the snapshot applies the `.env` file to every test run from that exe,
    which is the intent ("runs the same configuration this way").
  - No `.env` exists next to any build or gate exe today (checked: none under target/, none in `$TEMP/kk/te`), so gate
    outputs are unaffected.
- A child today sees the driver's environment plus the task's pairs. The worker is spawned with the driver's environment
  plus only the process-start pairs below, which every one of its tasks shares, so layer 1 plus layer 3 is the same set, plus the worker's own `TATIC_WORKER=1`, which nothing else reads.
  - Spawning it with a whole task's pairs would leak them into later tasks. A serve would then see a mine's
    `RULEMINER_LAWFILE` and `RULEMINER_BASE`.

### Process-start variables

Some variables are read once, when the process or its runtime starts, and a task cannot change them:

- `MIMALLOC_*`, read by mimalloc at load (the sweep sets `MIMALLOC_ALLOW_LARGE_OS_PAGES=0` for its children).
- `RUST_MIN_STACK` and `RUST_BACKTRACE`, cached by std at first use.

The driver therefore spawns the worker with the task's `MIMALLOC_*` and `RUST_*` pairs and no others. It respawns the
worker before any task whose `MIMALLOC_*` or `RUST_*` pairs differ from the running worker's. A sweep never varies them, so
it runs one worker.

mimalloc's own messages (`MIMALLOC_VERBOSE`, `MIMALLOC_SHOW_STATS`) go through the C runtime's stderr, not the redirected
handle, so a task's log would not get them. No sweep sets them.

## The worker

**The test.** `driver::worker`, `#[test] #[ignore]`, in the same exe. It is spawned as
`<exe> driver::worker --exact --ignored --nocapture`, with stdin and stdout piped and stderr inherited from the driver. Its
environment is the driver's, plus the process-start pairs below, plus `TATIC_WORKER=1`.

**The protocol** is one task per line on stdin and one reply per task on stdout.

- **Task:** `<test name>\t<log path>\t<KEY>=<VALUE>\t...\n`. The driver asserts that no name, path, key or value
  contains a tab or a newline, and the worker splits each pair at its first `=`.
- **Reply:** `\nWORKER ok\n` or `\nWORKER fail\n`, with a leading newline.
  - Single-threaded, libtest's formatter prints `test driver::worker ... ` with no newline before the test's own output.
    That happens with `--test-threads=1`, or when the affinity leaves one core.
  - The driver takes the first line that starts with `WORKER ` and ignores every other line, such as libtest's banner.
- **EOF on stdin:** the worker returns, so it never outlives its driver, even when the driver crashes.
- **Launched only by a driver.** The worker returns at once unless `TATIC_WORKER=1`, which only the driver sets when it
  spawns one. Otherwise `cargo test -- --ignored` would block forever on the worker reading a console stdin. The worker
  reads this flag with `std::env::var_os`, before any task, because it is the worker's own switch and not a task's
  configuration.

**Per task, on the worker's thread:**

1. Set `TASK_ENV` to the pairs and bump `TASK`.
2. Create the log file once. Flush `stdout`. Point the process's stdout and stderr at that one file.
   - On Windows, `SetStdHandle` sets both to the same handle, after saving the old handles with `GetStdHandle`.
     Elsewhere, `dup` saves fds 1 and 2, then `dup2` points both at the same fd.
   - The two streams then share one file offset, as the `try_clone`d handles do today (driver.rs ~99). Opening the file
     twice would make them overwrite each other.
   - Each is a small `extern` declaration (`kernel32` and libc are linked anyway), so no new dependency.
   - A throwaway probe (2026-10-15, rustc on this machine, file-backed stdout as the worker's pipe would be) checked the
     Windows path. After `SetStdHandle`, `println!` and `eprintln!` on a fresh thread wrote to the new file, and restoring
     the saved handles brought later output back. So std's stdout does not cache the handle. Its line buffer is flushed
     around each switch.
3. Run the task's function on a fresh `std::thread` named after the test, as libtest does.
   - Default `Builder`, so the stack follows `RUST_MIN_STACK` like libtest's test threads.
   - Join it. `Ok` means `ok`; a panic means `fail`, and its message has already gone to the log through the default
     panic hook.
4. Flush, restore the saved stdout and stderr handles, close the log, and write the reply.
5. After a `fail`, the worker exits. A panic can leave a `Mutex` poisoned or a pure memo half-filled, and a fresh process
   costs one launch. The driver respawns on the next task.

**Task functions.** The worker matches the name to the function: `search::rule_miner`,
`search::rule_set_kernel_check`, `machine::machine_state_line`, plus the test-only `driver::env_echo` (see Tests). Any other
name is a `fail` with a message in the log. Each
is the existing `#[test]` function, called directly; nothing about them changes except the deleted `load_exe_env` call.

**Driver side.** `struct Worker` in driver.rs:

- It holds the child process, its stdin, a `BufReader` on its stdout, and its process-start pairs, all behind a `Mutex`, so
  `run(&self, ...)` works from the `mine` and `serve` closures.
- `run(name, env, log) -> bool` has `child`'s contract and replaces it: it spawns or respawns as needed, writes the task,
  and reads up to the `WORKER` reply.
  - On a `WORKER fail` reply, the worker exits on its own. The driver reads its stdout to EOF, waits for it, returns `false`, and spawns a fresh
    one at the next task. The same applies after a memory-cap exit, if a cap is ever added (see Memory).
  - EOF before a reply (the worker died: abort, stack overflow, kill) returns `false` and drops the process. The task's
    log is then partial, as a crashed child's is today.
  - `serve` ignores `false` as it does today, and `mine` asserts.
- `Drop` closes stdin, reads the worker's stdout to EOF (libtest's closing lines must not hit a closed pipe), and waits for
  the process. So the worker never outlives the sweep, and `sweep_job.ps1`'s job object, which waits on the driver alone,
  still counts all of the worker's CPU. The worker inherits the driver's BelowNormal priority and affinity, as children
  do today.
- When a mine's `assert!` panics the driver, `Drop` runs during the unwind, so the worker still shuts down cleanly.
- `sweep` and `loop_stream` own one `Worker` and pass `&Worker` to `run_loop` and `machine_state`.
- `machine_state` runs `machine::machine_state_line` as a task, logs to `<out>/machine_state_<when>.log`, and reads the line
  back. That leaves `Worker` the only place the driver starts its own exe. It is skipped when `MACHINE_STATE=0`, which the gate sets, so it
  is outside the gate.
- `child` and its `Command` are deleted.

## Outputs and the gate

**Logs lose libtest's lines.** A task's log is what the test printed: it loses `running 1 test`, `test <name> ... ok`,
`test result: ...` and their blank lines. The driver parses none of them (it reads `CHECKED`, `RULEMINER chosen`,
`RULEMINER prefer` and `RULEMINER drop`).

**The gate.** `gate_cmp.sh` is committed (branch `shared-tree-encs`, unchanged from the session scratchpad it lived in) to
docs/runs/2026-10-12/scripts/, beside `hc_seq.sh`. It compares every file in the two sweeps' output trees,
salts 1 and 2. Before comparing, it normalizes:

- The tsvs' elapsed-seconds columns: it cuts them.
- In `.log` and `.txt` files: durations become `T`, the run tag becomes `RUN`, and "N filtered out" counts are blanked.

The worker branch then adds one rule: it drops libtest's harness lines.

- Gate: `hc_seq.sh` old against new, then `gate_cmp.sh`, with identical outputs on salts 1 and 2 (416 files each).
- One known, harmless difference is allowed: the `LEMMA_CACHE starts empty` stderr line can move among stdout lines in
  `lib_sbo3/mine_ref.log`. It already moved between two per-process runs (fill-loops and shared-tree-encs gates), so it
  is a stream interleaving, not a result.

**Determinism argument.** With the rule above, a task differs from a child only in:

- Pure memos that start warm. Outputs cannot depend on whether a pure lookup hits.
  - No budget counts lookups. Rewrite budgets count rewrite steps, and their memos are thread-locals.
  - No wall-clock cutoff reaches an output: the per-process gate already gives identical outputs under loads from 0% to
    over 90%, and warm memos only change timing.
- Process-wide addresses. `Term` equality and hashing are by pointer, `Ord` is structural, and no map's iteration order
  reaches an output (the "hash-rest" entry checked this); per-process runs already differ in addresses.

The gate is the check, and `task_state_is_classified` keeps the classification honest.

## Memory

A worker keeps what 169 short processes used to free at exit:

- The term table, which is never freed: a `Term` is a leaked `&'static`.
- The screens. 53.9 k distinct fills of 204 × 16 B make about 176 MB if they all land in one screen.
- The leaked `PerTask` values.

The plan's first step after it builds measures the worker's peak working set and the term table's size over a full sweep.

- If the peak stays under 2 GB, no cap is added.
- Otherwise the worker exits after any task that leaves its working set above the cap, and the driver respawns it. Only
  pure memos are lost, so outputs are unchanged.
- The machine has 62 GB, and other sessions run beside it.

## Expected gain, and how it is measured

The estimate is the empty-launch cost, about 9% of CPU and about 20% of wall time, plus the repeated fills (about 3%) and
the per-child exe hash (1.2%).

- Not saved: the per-task lemma-file reload, and the mines' thread start-up.
- Measured with `hc_rounds.ps1`: twelve alternating salt-1 sweeps, job CPU (the job object includes the worker) and wall,
  with load and Defender's state reported.
- Then a samply profile to see what is left outside own code.

## Parked

- **The lemma cache in memory across tasks.** It would save the per-task load, `lookup`'s file part.
  - It needs the in-memory copy to equal what a fresh load of the file would give at each task start. That holds when
    every write to the file comes from this worker, which the per-sweep lemma file makes true.
  - Also needed: an exact rule for when `LEMMA_CACHE starts empty` prints.
  - Measure what the reload costs first.
- **A persistent pool inside the miner.** It would take the 59 threads per mine.
- **Parallel tasks.** The driver is sequential, and each later step reads the files the earlier ones wrote.

## Risks

- **A static missed by the audit.** Covered by `task_state_is_classified` for church_bv and by the gate for outputs.
- **The stdout swap on other platforms.** Only Windows has been probed. Unix's `dup2` is the textbook equivalent and is
  covered by the same test (below).
- **A task's own child process inheriting the worker's stdin**, which is the task pipe. It could swallow task lines. The
  one task-spawned process today, `machine_state`'s PowerShell, uses `Command::output()`, whose stdin defaults to null.
  A future `spawn` or `status` from a task must set `stdin(Stdio::null())`. The worker's doc comment says so.
- **A task that leaves a detached thread running.** None today: every pool is scoped, and the PowerShell `Command` in
  `machine_state_line` is waited on. Such a thread would write into the next task's log.

## Tests

- `task_state_is_classified`: the source check above.
- `per_task_rebuilds_per_task`: a local `PerTask` read twice at one epoch builds once, and a read at the next epoch builds
  again.
  - It goes through `get_at(epoch, init)`, the function `get` calls with `TASK`. It must not bump the global `TASK`: the
    suite's other tests run in parallel in the same process, and a bump would reset their counters mid-test.
  - The environment overlay is covered by `worker_runs_tasks`, which runs its tasks in a worker process.
- `worker_runs_tasks` (ignored, run by hand and in the plan) uses a fourth task, `driver::env_echo`. It is an ignored test
  that prints `env_var(k)` for each name in `ECHO`, plus a per-process nonce (a process-wide `OnceLock` of the start time in nanoseconds; pids are reused too quickly on Windows to tell processes apart), and the worker's task table lists it beside the three real tasks.
  The test spawns a `Worker` and runs:
  1. `env_echo` with `ECHO=A,B` and `A=1`.
  2. `env_echo` with `ECHO=A,B` and `B=2`.
  3. A name the worker does not know.
  4. `env_echo` again.

  It asserts:
  - Task 2's log shows `A` unset: no leak from task 1.
  - The replies are ok, ok, fail, ok.
  - Each log holds only its own task's lines.
  - The nonces of tasks 1, 2 and 4: tasks 1 and 2 share one (the worker was reused), and task 4's differs (it was respawned).
- The sweep gate and `hc_rounds` (above).
