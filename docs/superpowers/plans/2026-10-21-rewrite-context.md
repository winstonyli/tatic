---
status: draft
---

# Rewrite context: an explicit `Job` instead of hidden state (C1 + C3)

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (inline). The tasks are sequential and each
> one changes signatures that the next one relies on, so this plan is not subagent-driven. Steps use checkboxes
> (`- [ ]`).

**Goal:** Pass church_bv's rewriter and miner state as an explicit `job: &Job` / `job: &mut Job` parameter. This
replaces the 15 per-job thread-locals and the per-task statics (`PerTask`, `PerTaskArc`, the task epoch). It also
splits the 830-line `rule_miner` closure nest into named structs and methods. The mined rules stay byte-identical,
except where a final task deliberately fixes a quirk.

**Why:** cleanup items C1 and C3 (`docs/superpowers/plans/2026-10-21-codebase-cleanup.md`). Today the state is
invisible in signatures. It gets saved and restored by hand at 9 sites. It is reset only because `driver::worker`
starts a fresh thread per task. And it hides at least five behaviour quirks (listed under "Quirks").

**Tech stack:** Rust (nightly, edition 2024), hashbrown. No new dependencies.

**Spec:** no separate spec. The design was settled in conversation on 2026-10-21 and is recorded under "Decisions"
below. That section is binding; where a task's text disagrees with it, the decision wins.

## Decisions (ruled 2026-10-21)

- **D1: one parameter.** Functions that only read take `job: &Job`. Functions that change the job take
  `job: &mut Job`. Code with no job (the driver process, its configuration) takes `setup: &Setup`. A job's
  `Rules` (rule table, preferences, the counting and tracing switches) cannot be changed in place, because they sit
  behind `Rc`. The field is private to `job.rs`. It is replaced only by `Job::with_rules`, which asserts on exit that
  the job's `id` and its installed rules are still the ones it set up. A source-scan test bans `mem::swap`,
  `mem::replace`, `mem::take` and `*job =` on a `Job` outside `job.rs`. Rejected alternatives: two parameters
  (`Cx` plus `&mut RewriteState`), `Pin<&mut Job>`, a view type with a lifetime, a single thread-local holding the
  job, and plan builders made generic over counting. Returning the counters as values is parked (`PARKED.md`, see
  Task 10).
- **D2: `Setup` absorbs all per-task state.** That is: the merged environment, the ablate set, `nops`, the rule set,
  the fixed rules, the lemma cache's task state and the task's result file. Each worker task builds one `Setup`, and
  task functions become `fn(&Arc<Setup>)`. `PerTask`, `PerTaskArc`, `TASK`, `TASK_ENV`, `RESULTS`, `task::begin`
  and `task::end` are deleted.
- **D3: thread-local caches of pure functions stay thread-local,** on an allow-list the guard test enforces:
  - `OP_CACHE`, `BUFS`, `TERMS`, `COUNTING`;
  - `CLOSED`, which `memo` keeps for its pure entries only;
  - `TREE_LAWS`, `CONSTANTS`, `BODIES` and encoding's `gen_memo` maps.

  `PARAMS`, and the lemma entries that `shared_lemma` keeps in `CLOSED` today, move into `Job`.
- **D4: stage order.** First split the miner (thread-locals untouched). Then introduce `Setup`. Then move the
  thread-locals into `Job` one group at a time.
- **D5: quirks are preserved exactly, written out explicitly,** until Task 9. Task 9 probes each one and fixes it
  in its own gated commit. A fix that changes mined rules stops for a ruling before it lands.

## Quirks (preserved through Task 8, fixed in Task 9)

- **Q1:** with `RULEMINER_THREADS` > 1, `prove`'s worker threads run `prove_rule` with no rule preferences. With one
  thread, `prove` runs inline under the base preferences that P0 installed (`search.rs:761-780` against `:492`).
- **Q2:** `shape_part` (`search.rs:308`) reads `RULEMINER_SHAPE_SALT` from the task's environment, while its caller
  `family_laws` (`:168`, `:210`) reads `RULEMINER_SHAPE` from the `env` closure it is given. In the driver, which
  passes a stage's env pairs through that closure (`write_laws`), a stage's own `RULEMINER_SHAPE_SALT` is ignored.
- **Q3:** `TREE_LAWS` (`machine.rs:382`) is keyed without `carry_cap`, which comes from the environment.
- **Q4:** `proving` (`rewrite.rs:1865`) does not save `REWROTE`. A proof's outermost `rewrite` therefore clears its
  caller's list, and the caller sees the proof's leftovers.
- **Q5:** the budget that P5's proofs run under (`search.rs:757`) is whatever the main thread's `RULE_BUDGET` holds
  there, not a configured value: what P1's last law left, unless P2–P4 rewrite on the main thread (Task 1 checks).
- Not a quirk: `check_replay` keeping the redo's `RULE_CONFLICTS` counts is documented as intended
  (`rewrite.rs:2423`) and stays.

## Global Constraints

- **Equality gate, after Tasks 1, 3, 4, 5, 6, 7 and each Task 9 fix:**
  1. `docs/runs/2026-10-18/scripts/salts_ab.sh <base exe> <new exe> 1 2 3 4 5`, rules `same` in all 15 loops.
  2. `threads_check.sh <new exe> {1,3,5}` passes.
  3. `miner_snap.sh` (Task 0) matches the base snapshots exactly.

  The sweep gate runs only `RULEMINER_FAST=1` and no preference phase (`driver.rs:36`, `:839`). `miner_snap.sh`
  covers the rest. The base exe is built from the plan's base commit (`main` at its start). Each gate is launched
  through `~/.claude/runs/run.ps1` (`-Kind gate`), which writes a row in `docs/runs.md`.
- **The suite stays green after every commit:**
  `cargo test --profile sweep --tests -j 8 -- --test-threads 8` (517 passed at 4ffe2a2). The count changes only by
  tests a task adds or deletes, and the commit message says which.
- **Build:**
  - `CARGO_TARGET_DIR="C:/Users/Winston Li/AppData/Local/Temp/rc_tgt"`, a separate target dir from main's
    `oracle_tgt`.
  - `-j 8`, or `-j 4` while a gate runs.
  - Gate exes are copied to `$TEMP/bv_rc<task>.exe`.
- **Work on a branch in a worktree:** `git worktree add ../tatic-rc -b rewrite-context main`. Ask before merging or
  pushing.
- **Line endings:** `driver.rs`, `machine.rs`, `search.rs` and `task.rs` are CRLF. Edit with the Edit tool, or use
  regexes with `\r?\n`.
- **Python:** never run python that reads stdin. Write a file and run `python -P f.py < /dev/null`.
- **No compatibility shims:** each task deletes what it replaces (old setters, statics, accessor functions) in the
  same commit.
- **Output text is unchanged:** every `println!` and `eprintln!` line, its order, and the order of the
  `setup.result` records stay byte-identical, apart from timing values.
- **Timing:** only Task 10 measures speed, quiet and sequential. It reports CPU load and Defender RTP alongside the
  numbers.

## Review Focus

1. **Implicit carry-over between miner phases on the main thread.** P0 installs the base rules and preferences, P1
   leaves a budget behind, `score_laws` leaves its preferences installed, and an inline `prove_any` leaves an empty
   table. Every main-thread rewrite must see exactly what it saw before. Tasks 1 and 4 write each carried value out
   as a named variable, and `miner_snap.sh` covers both the non-fast and the preference paths.
2. **The non-fast miner with several threads (Q1).** Only `miner_snap.sh`'s `nonfast4` configuration runs it.
3. **Lemma state across a job:** `PARAMS` is bound by `shared_lemma` and taken by `discharge`, and a worker thread
   proves several rules in one job. Task 7's test checks that a second `discharge` in the same job sees only the
   lemmas bound after the first.
4. **`with_rules` restores the outer rules on every exit except a panic** (a panic abandons the job, and the worker
   exits after any failure). Task 4's tests pin both the normal restore and the identity assertion.
5. **Tests that ran concurrently in one process shared `PerTask` epoch-0 state.** `Setup::process()` keeps that
   sharing for the one-test process. The lemma-cache `Save` guard stays per test, as today.

## File structure

- `tests/church_bv/job.rs` (new): `Setup`, `Job`, `RewriteState`, `Lemmas`, `NEXT_JOB`, and the scoped mutator
  `with_rules`. Holds `D1`'s guarantee, so it stays small (about 250 lines).
- `tests/church_bv/miner.rs` (new): `rule_miner`'s body as `Laws`, `Candidates`, `Scorer`, `Prover`, `Rounds`,
  `prefs_phase` and `Report`. `search.rs` keeps the `#[test] #[ignore] fn rule_miner()` entry, now a two-line wrapper.
- `tests/church_bv/rewrite.rs`: `Rules` (next to `RuleTable`, whose fields stay private). Every state-touching
  function gains `job`.
- `tests/church_bv/{search,machine,encoding,wasm,lemma_cache,driver}.rs`: callers.
- `tests/church_bv/task.rs`: keeps only `SharedMemo` and the guard test.
- `docs/runs/2026-10-21/scripts/miner_snap.sh` (new): the extra miner gate.
- Docs:
  - `docs/tier-cycle.md`, section "A persistent worker";
  - the module docs of `task.rs` and `driver.rs`;
  - `PARKED.md`;
  - the cleanup plan's C1 and C3 lines.

---

### Task 0: a miner gate for the paths the sweep gate skips (done 2026-10-21)

**Files:** `docs/runs/2026-10-21/scripts/miner_snap.sh`, its inputs in `docs/runs/2026-10-21/miner_snap_inputs/`, the
base snapshots in `docs/runs/2026-10-21/miner_snap_base/`.

The sweep gate runs only `RULEMINER_FAST=1`, reaches the preference phase (P9) never, and always runs through the
driver. `miner_snap.sh <exe> <outdir>` adds five configurations, about 5 minutes in all, each written as a
timing-free snapshot `<outdir>/<config>.txt` (lines `RULEMINER …`, timings replaced by `T`, `machine at` lines
dropped):

| config | what it runs |
|---|---|
| `nonfast1`, `nonfast4` | the non-fast miner (P5's kernel proofs) on 1 and 4 threads: the env of a cold cmp3d loop's first mine, with its law file (`laws_cmp3d_1.txt`, from the c7 gate's `s1_A`) and an empty base. 400 candidates, 67 chosen, about 73 s each |
| `pbase1`, `pbase4` | the same on `prefs_base.rules`, a pooled library that carries one preference (Q1 can only show with a base preference) |
| `pooled` | `driver::sweep` with `SWEEP=pooled:cmp3d SALT=1 LIB=miner_snap_inputs`: pooled units, then a mine whose only phase is P9. It learns one preference (gain +3001), about 18 s |

The libraries and `prefs_base.rules` come from `claude-runs\tatic\2026-10-17-join-cap\v1000_1`. The 2026-10-18
`lazy-join` libraries the draft named learned no preference in P9, so P9 chose nothing and its gain path went
untested. The draft's `RULEMINER_TRIALS` sizing is moot: a real law file already fills the 400-candidate cap.

**A/A on the base exe (main at 92b4be4, run `2026-10-21-t0-miner-snap-aa`):** 5/5 snapshots byte-equal across two
runs. `nonfast1` equals `nonfast4`. `pbase1` and `pbase4` choose the same 28 rules, but differ in work counts: 7
rounds score 1 more candidate (`round over 63 of 100` against 64), law evaluations 1060617 against 1063456, join
searches 33663 against 33674. With no base preference, the thread count changes nothing, so preferences are what
make it matter. This is Q1's baseline: P5's prove workers lack the base preferences, and possibly the speculative
proof workers (`search.rs:1156`) do too, which Task 9's Q1 probe must check.

The gate compares each configuration with its own base snapshot (`diff -r <outdir> miner_snap_base`, `*.txt`
only), never `pbase1` with `pbase4`.

### Task 1 (C3): split `rule_miner` into named parts, thread-locals unchanged

**Files:** Create `tests/church_bv/miner.rs`. Modify `search.rs:465-1300` (the body moves out), `main.rs`
(`mod miner;`).

**Interfaces, produced and kept by every later task:**
- `pub fn run()` in `miner.rs`, the whole miner. `search::rule_miner()` becomes `#[test] #[ignore] pub fn
  rule_miner() { crate::miner::run() }`. The driver's `task_fn` table still names `search::rule_miner`.
- Structs, from the census grouping. Fields are the cross-phase locals; their names stay as in the census table:
  - `struct Laws { stragglers, clean, scored, guard_w, kv, n }`, built by `fn laws(cfg: &MinerConfig, base_empty:
    bool) -> (Laws, i64)`. The `i64` is the budget P1 leaves behind (Q5), written out.
  - `fn candidates(laws: &Laws, cfg, base) -> (Vec<(Term, Term)>, HashMap<Term, Vec<(Term, Term)>>)` for P3–P4. The
    nested `abstractions`, `renum`, `bare` and the second `renum` become private free functions with distinct names
    (`renum_vars` and `renum_placeholders`).
  - `struct Prover { rules: Vec<(Term, Term)>, prefs: Option<Vec<Pref>>, budget: i64, n: usize }` with `fn
    prove(&self, rule) -> bool`. `prefs: None` means "install none" (`prove`'s workers, Q1). Inline at threads == 1
    it is also `None`, so it inherits what the thread has, which is the base preferences (Q1, written out in a
    comment). `prove_any` uses `Some(base_prefs)`.
  - `struct Scorer` holds `score_laws`, `summarize`, `count`, `guarded`, `value`, `all_laws`, `base_now`
    (`Mutex`), and the atomics `law_evals`/`law_reuses`. It is `Sync`, and the scoring workers borrow `&Scorer`.
  - `struct Rounds` holds `proofs`, `pending`, `assumed`, `speculate`, `spawn_req`, `picks`, `finished`,
    `state_memo`, `state_time`, `bound_time`, `scorings` and `skipped`, as plain fields under `&mut self`. Methods
    `pick`, `pick_kept`, `finish`, `settle` and `resolve`. `finish` takes `spawn: &dyn Fn(usize)` as today.
    `provable` becomes `Vec<usize>`, indices into an owned `cands`.
  - `fn prefs_phase(...)` for P9, and `struct Report` for P10.

- [ ] **Step 1: move, don't rewrite.** Each closure becomes a method or free function with the same body. A
  captured variable becomes a field or a parameter. `Cell` and `RefCell` locals that existed only because closures
  captured each other become plain fields. Keep:
  - every print and `task::result` call, in the same order;
  - the `phase(...)` labels;
  - the `_banner` and `_save` drop order (they stay locals of `run`, declared first);
  - the outer `tatic::kernel::scoped`.
- [ ] **Step 2: write the implicit carry-overs out as values.** P1's leftover budget (Q5) becomes the returned
  `i64`. P5 then sets `RULE_BUDGET` to it before its snapshot, exactly as the thread-local held it. First list every
  main-thread write of `RULE_BUDGET` between P1's end and `search.rs:757` (calls into `rewrite`, `rewrite_plan`,
  `prove_rule` from P2–P4 count); if there is one, the carried value is the budget after it, and Q5's text in this plan
  is corrected in the same commit. The base rules/prefs installed at P0 stay installed exactly as today.
- [ ] **Step 3: build and run the suite.** Expected: 517 passed, and clippy adds no new warnings for `miner.rs`
  (diff against `scratchpad/clippy_c18.txt`, recomputed on the worktree base).
- [ ] **Step 4: gate**, as in Global Constraints. Expected: rules `same` in 15/15, threads pass, snapshots equal.
- [ ] **Step 5: commit:** `C3: rule_miner as named parts in miner.rs`. Then update C3's line in the cleanup plan.

### Task 2: `job.rs` with `Setup` and an empty `Job` (TDD)

**Files:** Create `tests/church_bv/job.rs`. Modify `main.rs` (`mod job;`).

**Produces:**

```rust
pub struct Setup { env: Env, fixed: OnceLock<Vec<Rule>>, fixed_table: OnceLock<Vec<TableRule>>,
                   rule_set: OnceLock<Vec<(Term, Term)>>, pub lemmas: lemma_cache::TaskCache,
                   results: Mutex<Option<std::fs::File>> }
impl Setup {
    pub fn process() -> Arc<Setup>;                       // static PROCESS_SETUP: OnceLock<Arc<Setup>>; env as today's epoch 0
    pub fn for_task(pairs: Vec<(String, String)>, results: std::fs::File) -> Arc<Setup>;
    pub fn var(&self, k: &str) -> Option<&str>;          // was rewrite::env_var
    pub fn or<T: FromStr>(&self, k: &str, d: T) -> T;    // was env_or
    pub fn flag(&self, k: &str, d: bool) -> bool;        // was env_flag
    pub fn ablated(&self, name: &str) -> bool;           // was rewrite::ablated (parsed once at construction)
    pub fn nops(&self) -> usize;                          // was rewrite::nops
    pub fn result(&self, key: &str, value: impl Display); // was task::result
}
/// The task's environment from its three sources, later ones over earlier: the process's, `<exe>.env` for names the
/// process does not set, then the task's pairs. Names are upper-cased on Windows. Pure, so it is testable.
fn merge_env(process: impl Iterator<Item = (String, String)>, exe_env: Option<&str>, task: &[(String, String)]) -> HashMap<String, String>;

pub struct Job { id: u64, setup: Arc<Setup> }  // fields added by Tasks 4-7
static NEXT_JOB: AtomicU64 = AtomicU64::new(0);
impl Job {
    pub fn new(setup: Arc<Setup>) -> Job;
    pub fn setup(&self) -> &Arc<Setup>;
}
```

`rule_set`, `fixed_rules` and the fixed `TableRule`s are built at first use from `&Setup`, through `OnceLock` fields.
This keeps the driver process, which builds a `Setup` only to read configuration, from loading the lemma cache or
building rules. `TableRule` and `Rule` become `pub(crate)`.

- [ ] **Step 1: failing tests** in `job.rs`:

```rust
#[test]
fn task_pairs_override_the_process_and_exe_env_fills_only_unset_names() {
    let p = [("A".to_string(), "proc".to_string()), ("B".to_string(), "proc".to_string())];
    let env = merge_env(p.into_iter(), Some("B=file\nC=file\n"), &[("A".into(), "task".into())]);
    assert_eq!((env["A"].as_str(), env["B"].as_str(), env["C"].as_str()), ("task", "proc", "file"));
}

#[test]
fn flags_are_off_only_at_zero() {
    let s = Setup::from_env(merge_env([("X".to_string(), "0".to_string()), ("Y".to_string(), "no".to_string())].into_iter(), None, &[]));
    assert_eq!((s.flag("X", true), s.flag("Y", false), s.flag("Z", true)), (false, true, true));
}

#[test]
fn every_job_has_its_own_id() {
    let s = Setup::process();
    assert_ne!(Job::new(s.clone()).id, Job::new(s).id);
}
```

  (`Setup::from_env(HashMap)` is the private constructor that `process` and `for_task` share.)
- [ ] **Step 2: run them.** Expected: they fail to compile because `merge_env`, `Setup` and `Job` don't exist yet.
- [ ] **Step 3: implement.** Move `env_snapshot`'s logic into `merge_env`, and `switch_value` into `Setup::flag`.
  The old functions stay until Task 3 deletes them. This is the only task where old and new exist side by side,
  because Task 3 follows directly.
- [ ] **Step 4: run the tests.** Expected: the new tests pass and the suite count is 520.
- [ ] **Step 5: commit:** `job.rs: Setup and Job, unused yet`.

### Task 3: thread `Setup` through; delete the per-task statics

**Files:** all of `tests/church_bv/*.rs`.

The largest commit in the plan, mechanical and compiler-driven.

- [ ] **Step 1: the driver.**
  - `task_fn` returns `fn(&Arc<Setup>)`.
  - `worker` builds `Setup::for_task(env, results)` and runs the task on a fresh thread
    (`spawn(move || run(&setup))`), keeping the fresh thread for the D3 caches.
  - `task::begin`/`task::end` calls go.
  - The driver's own configuration reads (`LoopCfg::from_env`, `sweep`, `env_echo`, `cfg_var`, `write_laws`,
    `machine_state`) use `Setup::process()`.
  - Test entries (`search::rule_miner`, `rule_set_kernel_check`, `machine::pages_line`, `driver::env_echo`) become
    `#[test] fn x() { x_task(&Setup::process()) }`, with `x_task(setup: &Arc<Setup>)` holding the body.
- [ ] **Step 2: the rewriter and its callers.**
  - Every function that reads `env_var`, `env_or`, `env_flag`, `ablated`, `nops`, `carry_cap`, `join_visit`,
    `rule_set`, `fixed_rules`, `lemma_cache::*` or `task::result`, directly or through a callee, gains `job: &Job`.
    Functions that already need `&mut Job` in a later task still take `&Job` here; Tasks 4–7 upgrade them.
  - Functions outside any job take `setup: &Setup` instead: `MinerConfig::from_env` becomes
    `MinerConfig::new(&Setup)`, and the same goes for `family_laws`'s env closure.
  - Each thread that rewrites (the miner's main thread, its four `thread::scope` spawn sites, tests that spawn) makes
    its own `Job::new(setup.clone())`.
  - Tests start with `let job = &Job::new(Setup::process());`.
- [ ] **Step 3: delete.**
  - In `rewrite.rs`: `ENV`, `env_snapshot`, `env_name` (moves to `job.rs`), `env_var`, `env_or`, `env_flag`,
    `switch_value`, `ablated`'s `SET`, `rule_set`'s `SET`, `fixed_rules`' `RULES` and `RuleTable::new`'s `FIXED`.
  - In `lemma_cache.rs`: `PROCESS`, `RECORDED`, `HITS`, `BUILT`, `SKIPPED` and `recheck`'s `R`. They become
    `lemma_cache::TaskCache`, a field of `Setup`; `Save` holds an `Arc<Setup>`.
  - In `task.rs`: `TASK`, `TASK_ENV`, `RESULTS`, `begin`, `end`, `result`, `task_env`, `PerTask`, `PerTaskArc` and
    `per_task_rebuilds_per_task`.
  - `TRACE_RULES` and `RULE_CONFLICTS` are job state, so they stay until Tasks 4 and 6, but no longer as `PerTask`:
    for this one commit they become `thread_local!`. That matches what a fresh task thread sees today, except across
    the miner's threads. Verified 2026-10-21: `RULE_CONFLICTS` is armed only at `search.rs:1240` (P9, disarmed by the
    `take()` two lines on, around one single-threaded `score_laws`) and `search.rs:2305` (`rule_set_kernel_check`, no
    threads), so no spawned thread counts into it. `TRACE_RULES` is set and read on one thread per use; grep its sites
    again before converting.
- [ ] **Step 4: checks.**
  - `grep -n 'PerTask\|env_var(\|env_or(\|env_flag(\|task::result\|task_env' tests/church_bv/*.rs`: expected empty
    (111 sites today, 31 of them in `driver.rs`).
  - `grep -n 'Setup::process()' tests/church_bv/*.rs`: for each site, confirm that no task function reaches it. A
    task that read `Setup::process()` would silently lose its task's env pairs, which the old `ENV` merged in. Allowed:
    the driver's own loop (`sweep`, `LoopCfg`, `write_laws`, `cfg_var`, `machine_state` before it sends a task), the
    `#[test]` wrappers, and tests.
  - Suite: expected 520 minus `per_task_rebuilds_per_task`, so 519.
  - Clippy: no new warnings.
- [ ] **Step 5: gate.** Expected: equal.
- [ ] **Step 6: commit:** `C1 step 1: Setup replaces the per-task statics`, listing what was deleted.

### Task 4: `Rules` into the job (`RULE_TABLE`, `RULE_PREFS`, `SCORE_ONLY`, `TRACE_RULES`)

**Files:** `rewrite.rs` (`Rules`, `rule_step`, `Plan::new`, `join_search` and the other readers), `job.rs`
(`rules` field, `with_rules`), callers.

**Produces:**

```rust
// rewrite.rs
#[derive(Clone)]
pub struct Rules { table: Rc<RuleTable>, prefs: Rc<hashbrown::HashSet<Pref>>, score_only: bool, trace_rules: bool }
impl Rules {
    pub fn new(setup: &Setup, mined: Vec<(Term, Term)>) -> Rules;    // set_extra_rules' sort + RuleTable::new; no prefs, both switches off
    pub fn with_mined(&self, setup: &Setup, mined: Vec<(Term, Term)>) -> Rules;  // keeps prefs and switches
    pub fn with_prefs(&self, prefs: Vec<Pref>) -> Rules;            // set_rule_prefs' rule: a later pair replaces the reverse one
    pub fn counting(&self, on: bool) -> Rules;
    pub fn tracing(&self, on: bool) -> Rules;
    pub fn mined(&self) -> &[(Term, Term)];
    pub fn score_only(&self) -> bool;
    pub(crate) fn is(&self, other: &Rules) -> bool;                   // Rc::ptr_eq on both Rcs, and equal switches
}
// job.rs
impl Job {
    pub fn rules(&self) -> &Rules;
    /// `f` with `rules` installed; the job's rules are put back after. Panics if `f` left this job holding other rules,
    /// or swapped it for another job.
    pub fn with_rules<T>(&mut self, rules: Rules, f: impl FnOnce(&mut Job) -> T) -> T {
        let (id, outer) = (self.id, std::mem::replace(&mut self.rules, rules));
        let installed = self.rules.clone();
        let out = f(self);
        assert!(self.id == id && self.rules.is(&installed), "a job's rules were replaced outside with_rules");
        self.rules = outer;
        out
    }
}
```

`Job::new` installs `Rules::new(&setup, vec![])`, which is today's thread-local default.

- [ ] **Step 1: failing tests** in `job.rs`:

```rust
#[test]
fn with_rules_puts_the_outer_rules_back() {
    let s = Setup::process();
    let mut job = Job::new(s.clone());
    let outer = job.rules().clone();
    let inner = Rules::new(&s, vec![(parse_term("add(x, 0)"), parse_term("x"))]);
    let seen = job.with_rules(inner.clone(), |job| job.rules().is(&inner));
    assert!(seen && job.rules().is(&outer));
}

#[test]
#[should_panic(expected = "replaced outside with_rules")]
fn with_rules_catches_a_swapped_job() {
    let s = Setup::process();
    let (mut a, mut b) = (Job::new(s.clone()), Job::new(s.clone()));
    a.with_rules(Rules::new(&s, vec![]), |job| std::mem::swap(job, &mut b));
}
```

- [ ] **Step 2: run them.** Expected: they fail to compile, since `Rules` and `with_rules` don't exist yet.
- [ ] **Step 3: implement and convert.**
  - Every `set_extra_rules(x) … set_extra_rules(vec![])` pair becomes `job.with_rules(job.rules().with_mined(setup, x), |job| …)`.
    The same goes for prefs (`with_prefs`), `SCORE_ONLY` (`counting`) and `TRACE_RULES` (`tracing`).
  - Readers take `job.rules()`. `Plan::new` and the plan constructors take `job: &Job`.
  - `rule_step_in(t, &RuleTable)` becomes `rule_step_in(job: &mut Job, t)`. It clones the `Rc<RuleTable>` once per
    call (`let table = job.rules().table.clone();`) only if the borrow checker requires it; otherwise it reads through
    a local `&Rules` copied out before the mutations. Prefer the borrow; measure in Task 10 if the clone was needed.
  - `set_extra_rules`, `set_rule_prefs`, `RULE_TABLE`, `RULE_PREFS`, `SCORE_ONLY` and `TRACE_RULES` are deleted.
- [ ] **Step 4: the miner's carry-overs.** For each main-thread call that rewrites (P1's `rewrite_plan` and
  `rewrite`, `state`/`score_laws`, inline `prove`/`prove_any`, P9's `gain`), write in a comment which rules,
  preferences and switches the thread-locals held at that point in today's code, and install exactly those. Known
  cases:
  - P1 runs under base rules and base prefs.
  - Inline `prove` (threads == 1) runs under base rules and base prefs (Q1).
  - The workers' `prove` runs under base rules and no prefs (Q1).
  - `prove_any` runs under base rules and base prefs.
  - `score_laws` runs under `base_now + extra` with its `prefs`. Its "leaves prefs installed" has no reader after it,
    since every later main-thread rewrite goes through `score_laws` or `prove_any`, which install their own. Verify
    this by listing the calls.
- [ ] **Step 5: suite, clippy, gate.** Expected: suite 521, no new warnings, gate equal.
- [ ] **Step 6: commit:** `C1 step 2: the job's rules, replaced only through with_rules`.

### Task 5: `RewriteState` and `blocked` (`REWRITE_PATH`, `REWROTE`, `CUT_LOW`, `CYCLE_CUTS`, `REWRITE_MEMO`, `RULE_TRACE`, `RULE_BUDGET`, `MACHINE_FALLBACKS`, `PROVING`)

**Produces:**

```rust
pub struct RewriteState {
    pub path: Vec<Term>, pub rewrote: Vec<Term>, pub cut_low: usize, pub cycle_cuts: u64,
    pub memo: Option<RewriteMemo>, pub trace: Option<Vec<(Term, Fired)>>, pub budget: i64, pub fallbacks: u64,
}
impl Default for RewriteState { /* cut_low: usize::MAX, budget: i64::MAX / 2, the rest empty or 0 */ }
// Job gains: pub rw: RewriteState, pub blocked: Vec<RuleKey>
```

- [ ] **Step 1: failing test** (`rewrite.rs`). A rule proved inside a rewrite does not change the caller's
  budget, trace or fallbacks: run `proving` from a job whose budget is 777, whose trace is `Some(vec![])` and whose
  fallbacks are 5, then assert all three are unchanged and `job.blocked` is back to its length before. Write it
  against the new API. It fails to compile until Step 2.
- [ ] **Step 2: convert.**
  - Each `X.with(|c| …)` becomes the field.
  - `proving(blocked, f)` becomes `proving(job, blocked, f: impl FnOnce(&mut Job) -> T)`. It swaps in a fresh
    `RewriteState { budget: 10_000, rewrote: mem::take(&mut job.rw.rewrote), ..Default::default() }` and, after `f`,
    moves `rewrote` back into the restored state (Q4, preserved: the proof shares its caller's list).
  - `rewrite_memo` and `check_replay` keep their field-by-field save and restore. They restore subsets, which a
    whole-struct swap would get wrong.
  - Every before/after read of `MACHINE_FALLBACKS` in `search.rs` becomes `job.rw.fallbacks`.
- [ ] **Step 3: suite, clippy, gate.** Expected: suite 522, gate equal.
- [ ] **Step 4: commit:** `C1 step 3: the rewrite state in the job`.

### Task 6: join state and conflicts (`JOIN_STORE`, `JOIN_COST`, `RULE_CONFLICTS`)

- [ ] **Step 1: convert.**
  - `Job` gains `pub join_store: Option<JoinStoreUse>`, `pub join_cost: JoinCost` and
    `pub conflicts: Option<HashMap<Pref, u64>>`.
  - `set_join_store` and `frozen_join_store` become field access, plus `JoinStore::frozen(&self)` where a clone is
    taken.
  - `JoinCost::now` becomes `job.join_cost`, and `add_since` stays as a method on values.
  - `print_rule_conflicts(job)` takes the map.
  - The scoring workers set `job.join_store = Some(Read(frozen))` on their own job. Their join-cost delta is their
    job's whole `join_cost`, since the job is fresh, as the thread was.
- [ ] **Step 2: suite, clippy, gate.** Expected: suite unchanged, gate equal.
- [ ] **Step 3: commit:** `C1 step 4: join state and conflict counts in the job`.

### Task 7: lemmas (`PARAMS` and `shared_lemma`'s entries)

**Produces:** `pub struct Lemmas { closed: HashMap<String, (PExpr, PExpr)>, params: Option<(Postulates, Vec<(Scope, Option<PExpr>)>)> }`
in `job.rs`; `Job` gains `pub lemmas: Lemmas`. `shared_lemma(job: &mut Job, key, build)` and
`discharge(job: &mut Job, body)`. `memo` keeps `CLOSED` for its pure entries.

- [ ] **Step 1: check that `memo`'s and `shared_lemma`'s keys don't collide.** List every `memo(` and
  `shared_lemma(` key format. If one is used by both, stop and report.
- [ ] **Step 2: failing test.** In one job, bind lemma A, `discharge` a body, bind lemma B, `discharge` again.
  The second discharged term must apply only B's proof. It fails to compile until Step 3.
- [ ] **Step 3: convert.**
  - `PARAMS` is deleted.
  - Callers of `witnessed`, `holds`, `Compiler::proof`, `if_law`, `if_good`, `prove_checked`, `add_tree_law` and
    `tree_proof` gain `job` where the compiler asks.
  - `encoding.rs`'s `holds`, which reads `PARAMS`, takes `job: &Job`.
- [ ] **Step 4: suite, clippy, gate.** Expected: suite 523, gate equal.
- [ ] **Step 5: commit:** `C1 step 5: lemma parameters in the job`.

### Task 8: the guard test and docs

- [ ] **Step 1: rewrite `task_state_is_classified`** (it moves to `job.rs` and is renamed
  `hidden_state_is_classified`). It fails on:
  - any `thread_local!` static in church_bv not on D3's allow-list, by name: `OP_CACHE`, `BUFS`, `TERMS`,
    `COUNTING`, `CLOSED`, `TREE_LAWS`, `CONSTANTS`, `BODIES`, and `gen_memo`'s statics;
  - any mutable process-wide static other than `SharedMemo`s and the list `TABLE`, `CACHE`, `ID`, `NONCE`,
    `NEXT_JOB`, `PROCESS_SETUP`;
  - outside `job.rs`, any line matching `mem::(swap|replace|take)\(\s*(&mut\s+)?\*?job\b` or `^\s*\*job\s*=`.

  Keep the existing `flagged` unit tests, and add one per new rule with a line that must trip it.
- [ ] **Step 2: run.** Expected: the suite passes, at 523 plus the guard tests added in Step 1. Then add `thread_local! { static ZZ: Cell<u8> = … }` to
  `rewrite.rs` temporarily and confirm the guard fails, then remove it.
- [ ] **Step 3: docs.**
  - `docs/tier-cycle.md`, "A persistent worker": the worker now builds a `Setup` per task. The fresh thread remains
    only for D3's caches.
  - `task.rs` and `driver.rs` module docs.
  - The comments that named the deleted statics (`grep -rn 'RULE_BUDGET\|SCORE_ONLY\|REWRITE_MEMO\|PerTask' tests docs/*.md README.md`;
    the plan files under `docs/superpowers` keep their history).
  - Cleanup plan: C1 done, and C17's `SCORE_ONLY` comment nit is resolved.
- [ ] **Step 4: commit:** `C1 step 6: the guard covers thread-locals and job swaps; docs`.

### Task 9: the quirks, one commit each

For each of Q1–Q5:
1. Make the fix, with a test where one is meaningful.
2. Build, and run the gate against the Task 8 exe.
3. If outputs are equal, commit (`Q<n>: …`).
4. If mined rules change, write the difference (which loops, M before and after) into `docs/tier-cycle.md` and stop
   for a ruling before committing.

- [ ] **Q1:** `prove` passes the base preferences on every thread (`Prover.prefs = Some(base_prefs)`). Expected:
  `nonfast4` changes only if the preferences matter to proofs. `nonfast1` is unchanged.
- [ ] **Q2:** `family_laws`'s closure returns `usize` and cannot carry a salt string. It becomes
  `env: &dyn Fn(&str) -> Option<String>`, with the numeric reads parsed at the call, and `shape_part` takes the salt
  from it. Expected: no change, since no stage sets `RULEMINER_SHAPE_SALT` today (grep `driver.rs` to confirm).
- [ ] **Q3:** `TREE_LAWS`'s key gains `carry_cap`. Within one process the cap is fixed per task, so expected: no
  change.
- [ ] **Q4:** `proving` gives the proof a fresh `rewrote` and leaves the caller's alone. First add a
  `debug_assert!(job.rw.rewrote.is_empty())` at entry and run the debug suite (`cargo test --tests -j 8`; the sweep
  profile has no debug assertions) to learn whether a proof ever starts inside a rewrite. If it never does, the fix
  cannot change outputs.
- [ ] **Q5:** P5's proofs run with `cfg.steps` (or `i64::MAX / 2` with an empty base, as P1 uses). This is a
  behaviour decision if outputs change.

### Task 10: timing, parked item, close

- [ ] **Step 1: quiet timing.** Sequential A/B of the base exe against the Task 9 exe, using `salts_ab.sh` with
  salts 1–3 after an A/A pair. Require `\Processor(_Total)` under ~20% and report Defender RTP. Record the result
  in `docs/tier-cycle.md` with the run ids. Expected: the same or faster, since environment reads on hot paths
  (`ablated`, `nops`, `join_visit`) become field reads. If it is slower by more than noise, profile (SAMPLY.md)
  before closing.
- [ ] **Step 2:** update the `PARKED.md` entry "Counters as return values" (added with this plan) with the delta-site
  count after Task 5.
- [ ] **Step 3:** set this plan's `status: done`, update the cleanup plan's C1 and C3 lines, and ask about merging.
