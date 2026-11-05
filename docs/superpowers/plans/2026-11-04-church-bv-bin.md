---
status: done
---

# `church-bv` binary Implementation Plan (TB1 step 2)

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (inline). Steps use checkboxes.

**Goal:** `church-bv <subcommand>` runs the 8 entry points the scripts and tools name; the sweep worker is `church-bv worker`;
all existing tests keep their names and results.

**Architecture:** one `entry` module (table + `main`), a 10-line `main.rs`, one declared re-entry value in `driver.rs`, eight
bodies moved from `#[test]` fns to plain fns, then the callers repointed.

**Tech Stack:** Rust 2024 workspace, bash, `~/.claude/runs/run.ps1`, `~/.claude/samply/icount.ps1`.

**Spec:** `docs/superpowers/specs/2026-11-04-church-bv-bin-design.md`

## Global Constraints

- All 749 current test names still exist; the only list difference is the added tests. Profiles stay in the root manifest.
- Configuration stays in the environment; no argument parser, no new dependency. No push, tag or bump.
- Commits end with the Co-Authored-By line; long runs through `run.ps1`; Edit tool for files; `git diff --stat` before committing.

## Review Focus

- Stack: an entry that recurses deeply runs on a spawned default-size thread, as under libtest, not on the 1 MiB main thread (Task 2 test pins the thread; Task 3 Step 4 runs a real sweep through it).
- Exit status: a panicking entry exits 101, an unknown subcommand exits 2, success 0 (Task 3 tests).
- A worker started with the wrong command: `Worker::spawn` default equals today's libtest form (Task 2 test); the bin declares
  `["worker"]` before any spawn (Task 3 test: `church-bv worker` with closed stdin exits 0).
- A script or tool still passing `driver::x --exact --ignored` to the bin (Task 4 greps the whole repo).
- `<exe>.env` and the mimalloc settings: the bin carries the allocator (Task 3) and reads `church-bv.exe.env` like any exe.

---

### Task 1: Baseline

- [ ] **Step 1:** test list: `cargo test -j 4 --workspace -- --list 2>/dev/null | grep ': test' | sort > .superpowers/rs/tb1b-before.txt`
  (expected 749).
- [ ] **Step 2:** inventory the callers: `git grep -nE 'driver::(sweep|loop_stream|worker)|proof_cost_split|rule_set_kernel_check|ctx_fit|overlap_report|q1_report|--exact|--ignored' -- scripts tools crates/church-bv README.md docs/TOUR.md`;
  save the list in the ledger; every hit is repointed, kept (a test) or ruled in Task 4.
- [ ] **Step 3:** choose the check sweep: the cheapest `driver::sweep` configuration (read `scripts/test_gate.sh` and `docs/tier-cycle.md`
  "work counts"; env `SWEEP`, `SALT`, `SWEEP_OUT`, a small cut of the stream) that runs in about a minute. Run it with the saved
  test exe from step 1 (`church_bv_tb1_new.exe` in the scratchpad) as
  `SWEEP_OUT=<dir> ... <exe> driver::sweep --exact --ignored --nocapture`; keep its stdout and result files as the reference.
  Run it twice: the `WORK` lines must repeat exactly; if not, rule on what the check compares instead.

### Task 2: `entry` module, moved bodies, declared re-entry (tests first)

**Files:** create `crates/church-bv/src/entry.rs`; modify `lib.rs` (`pub mod entry;`), `driver.rs`, `search.rs`, `ctx_scorer.rs`.

**Interfaces — Produces:** `pub fn main() -> std::process::ExitCode`; `fn lookup(name: &str) -> Option<fn()>`;
`pub const NAMES: [&str; 8]`; in `driver.rs`: `pub fn declare_reentry(args: &[&str])` and `fn reentry() -> Vec<String>`.

- [ ] **Step 1: Failing tests** in `entry.rs`: `names_are_unique_and_all_resolve` (every `NAMES` entry looks up to `Some`, no
  duplicates, `lookup("nonsense")` is `None`); in `driver.rs`: `reentry_defaults_to_the_libtest_form` (`reentry()` equals
  `["driver::worker","--exact","--ignored","--nocapture"]` when nothing was declared); `entry.rs`: `entries_run_off_the_main_thread`
  (the helper `run_on_thread(f)` runs its closure on a thread other than the caller's and returns the closure's `Result`; it spawns with the default stack size, which is what libtest gives a test).
  Run `cargo test -p church-bv --lib entry:: reentry` — Expected: FAIL (does not compile: items missing).
- [ ] **Step 2: Implement.** Eight `fn run_<name>()` in `driver` (`run_sweep`, `run_loop_stream`, `run_worker`), `search`
  (`run_proof_cost_split`, `run_rule_set_kernel_check`), `ctx_scorer` (`run_ctx_fit`, `run_overlap_report`, `run_q1_report`),
  each holding the body of the like-named test, which becomes `#[test] #[ignore] fn x() { run_x() }` under its old name; the
  `worker` test keeps its `TATIC_WORKER` early return. `entry.rs`: the table, `lookup`, `run_on_thread`, `main` (declare
  `["worker"]`; argument 1 selects; 2 for none or unknown, printing the names; 101 on a panic; the entry's output is not buffered).
  `driver.rs`: a `OnceLock<Vec<String>>` behind `declare_reentry` (a second call panics) and `reentry()`; `Worker::spawn` uses
  `reentry()` for its arguments, still setting `TATIC_WORKER=1`.
- [ ] **Step 3:** Run the Step 1 command — Expected: PASS. Then `cargo check -j 4 --workspace --all-targets` — Expected: clean
  apart from the 2 known warnings; note any new dead-code warning for Task 3's ruling on the crate-level attribute.
- [ ] **Step 4:** test list equals `tb1b-before.txt` plus exactly the 3 new names (`entry::names_are_unique_and_all_resolve`, `entry::entries_run_off_the_main_thread`, `driver::reentry_defaults_to_the_libtest_form`). Commit `church-bv: entry module, entry bodies as plain fns, declared re-entry`.

### Task 3: The bin (tests first)

**Files:** create `crates/church-bv/src/main.rs`, `crates/church-bv/tests/bin.rs`; modify `crates/church-bv/Cargo.toml` only if needed.

- [ ] **Step 1: Failing tests** in `tests/bin.rs` (spawn `env!("CARGO_BIN_EXE_church-bv")`): `no_subcommand_exits_2_and_lists_names`
  (stderr or stdout contains every `NAMES` entry, status 2); `unknown_subcommand_exits_2`; `worker_with_closed_stdin_exits_0`
  (stdin null); `a_panicking_entry_exits_101` is unit-level in `entry.rs` through `run_on_thread` returning `Err` (add there).
  Run `cargo test -p church-bv --test bin` — Expected: FAIL (no such binary target).
- [ ] **Step 2: Implement** `main.rs`: `#[global_allocator] static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;` and
  `fn main() -> std::process::ExitCode { church_bv::entry::main() }`; a comment says the lib's allocator is `cfg(test)` only.
- [ ] **Step 3:** Run the Step 1 command — Expected: PASS. `cargo check -j 4 --workspace --all-targets`; rule on the crate-level
  attribute: delete it only if no non-test warning remains, else keep it and reword its comment to say what is still test-only.
- [ ] **Step 4:** Equivalence on the Task 1 sweep: `cargo build -p church-bv`, run `church-bv sweep` with the same environment;
  `diff` its `WORK` lines and result files against the reference — Expected: identical. Commit `church-bv: the church-bv binary`.

### Task 4: Callers

- [ ] **Step 1:** `tools/runs/src/gate.rs` `sweep_args` to `["sweep"]` and its doc comment; `time.rs:89` args to
  `["proof-cost-split"]`; fix the tests that assert them. `cargo test --manifest-path tools/runs/Cargo.toml` — Expected: 45 pass; rebuild release.
- [ ] **Step 2:** scripts: the five named in the spec and `test_gate.sh`: `"$exe" driver::sweep --exact --ignored --nocapture`
  becomes `"$exe" sweep`, likewise for the others, with `exe` pointing at `target/<profile>/church-bv.exe` (copy as the script copies
  today). Every hit of Task 1 Step 2 is handled; `git grep -nE -- '--exact' -- scripts tools` lists nothing that targets the bin.
- [ ] **Step 3:** run `scripts/test_gate.sh` through `run.ps1 -Kind gate -Affinity CFF -Name tb1b-test-gate -Detach` with a bounded
  watcher — Expected: 0 failed. Commit `church-bv: tools and scripts call the binary`.

### Task 5: Docs

- [ ] **Step 1:** `docs/TOUR.md`: `entry.rs` and `main.rs` in the church-bv module list, the line on how a run starts; README
  lines 77, 111, 137 and the sweep/gate commands; module docs that tell a reader to run `driver::x --exact --ignored` for the 8
  entries; `PARKED.md`: delete the step 2 entry. `tour_check.sh` and `cite_check.sh` pass.
- [ ] **Step 2:** commit `docs: church-bv binary`.

### Task 6: Checks and close

- [ ] **Step 1:** test list = baseline + 7 new names (3 in Task 2, 4 in Task 3); `cargo test -j 4 --workspace --lib --bins` passes; full suite through
  `run.ps1 -Kind probe -Name tb1b-suite -Affinity CFF -MaxMemGB 12 -Detach` (expected 701 + the new tests passed, 0 failed).
- [ ] **Step 2:** counts: `icount.ps1 -Cpu 4 -Runs 6` on the Task 1 sweep, old test exe against `church-bv.exe`; within the A/A spread.
- [ ] **Step 3:** one Sonnet whole-branch review with the Review Focus; one fix pass. Append the outcome to the TB1 item in the
  cleanup plan, set this plan and the spec `status: done`, closing report.
