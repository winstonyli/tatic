---
status: active
---

# `church-bv` binary (TB1 step 2)

Parked item "`church-bv` binary (TB1 step 2)" in `PARKED.md`; step 1 is `docs/superpowers/specs/2026-11-04-church-bv-crate-design.md`.
Facts below are from a read-only look on 2026-11-04 (commit 999b51b); the plan's first task re-verifies them.

## Intent

Drivers, scripts and `tools/runs` run `church_bv` by finding a hash-named test exe and passing libtest arguments
(`<exe> driver::sweep --exact --ignored --nocapture`). The sweep's worker re-runs the same exe the same way. After step 2 the
entry points are subcommands of a real binary, `church-bv sweep`, at a stable path (`target/<profile>/church-bv.exe`), and
the worker is `church-bv worker`. Nothing else about the research code changes.

## Decided by the user (2026-11-04)

- g1: two steps; step 2 settled after step 1 (this spec).
- s1: entry points only. Subcommands: `sweep`, `worker`, `loop-stream`, `proof-cost-split`, `rule-set-kernel-check`, `ctx-fit`,
  `overlap-report`, `q1-report` (the tests that scripts, `tools/runs` or the README name; `rule_miner` and the other ~38
  `#[ignore]`d tests stay ignored tests).
- u3: the entry declares how this exe is re-entered as a worker. Default (the test exe): the libtest arguments, as today. The
  bin's `main` declares `["worker"]`. No `cfg(test)` branch in `Worker::spawn`, no tests moved.

## Design

**Files.** New `src/entry.rs` (the table and `main`), new `src/main.rs` (the bin: the shipping `#[global_allocator]` and a call
into `entry`), new `tests/bin.rs` (runs the built bin, `CARGO_BIN_EXE_church-bv`). Package `church-bv` gains no dependency
(`mimalloc` is already one).

**The mechanism.** `entry.rs` holds one table of `(subcommand, fn())` and one `main() -> ExitCode`: it declares the re-entry
arguments, looks the first argument up, runs the entry on a spawned thread (default stack size, as libtest gives a test; the
main thread of a Windows exe has 1 MiB and the code recurses deeply), and exits 0, or 101 on a panic as a failed test does.
No arguments or an unknown one prints the table and exits 2. Configuration stays in the environment (`Setup::process()` reads
it); no flags, no argument parser.

**Entry bodies.** A `#[test] #[ignore] fn x()` is not compiled outside test builds, so each of the 8 bodies becomes a plain `fn
run_x()` in its module and the test keeps its name and calls it (`driver::sweep` still exists, so the test-name list only
grows). The table points at the `run_x`. `worker` keeps its `TATIC_WORKER` gate in the test wrapper only; `run_worker` has none.

**Re-entry.** `driver.rs` gains one process-wide value, set at most once (a second set is a panic): the arguments that start this
exe as a worker. `Worker::spawn` reads it (default `["driver::worker", "--exact", "--ignored", "--nocapture"]`). The other
self-spawns (`job.rs`, `work.rs`) run only inside tests and keep the libtest form.

**Visibility.** Only `entry` is `pub`; the bin calls `church_bv::entry::main()`. Code the entries reach stops being dead in a
non-test build; the rest still warns, so the crate-level `#![cfg_attr(not(test), allow(dead_code, unused_imports))]` stays
unless the plan's count shows nothing left (my correction of step 1's "step 2 deletes it").

**Callers repointed.** `tools/runs/src/gate.rs` `sweep_args` (`["sweep"]`) and its test, `tools/runs/src/time.rs:89`
(`proof-cost-split`), `scripts/{ctx_dump,ctx_fit,ctx_overlap,ctx_q1,streams_ab}.sh`, `scripts/test_gate.sh` where it names the
args, `README.md` (build with `cargo build -p church-bv [--profile sweep]`, run the bin), the module docs that name `driver::x
--exact --ignored` as the way to run, `docs/TOUR.md` (new module `entry`, `main.rs`, the flow line for starting a run).

**Consequences.** (1) The exe is named `church-bv.exe`, not `church_bv-<hash>.exe`, and is rebuilt per profile; the gate's arm
cache (a hash of exe bytes and its `.env`) misses once. (2) A gate with the pre-step-2 test exe as `old` cannot run once: it
cannot take `sweep`. The equivalence check for the step is by work counts instead (below). (3) `tools/runs/src/cmp.rs` drops
libtest lines (`running N tests`, `test x ... ok`, `test result`) before comparing logs; the bin prints none, so the filter
matches nothing and logs compare as before.

## Non-goals

An argument parser or flags; turning the other ignored tests into subcommands; changing a sweep's result or its work counts;
moving `tools/runs` onto a library; renaming the 749 tests.

## Anti-goals

A sweep that behaves differently under the bin (stack, allocator, environment, the `<exe>.env` file, exit code); a
worker that quietly runs the wrong command; a script still calling the old exe form and failing late.

## Verification

Work counts: one fixed, small `driver::sweep` configuration run by the old test exe (saved in step 1) and by `church-bv sweep`
gives identical `WORK` lines (`work::line`, deterministic) and identical result files. The old 749 names all still exist; the
new names are exactly the added tests. `cargo check --workspace --all-targets`; the suite; `scripts/test_gate.sh`; `tools/runs`
tests; `tour_check`, `cite_check`; a count of the bin against the test exe on that sweep (ICOUNT.md) within the spread.

## Left to the builder

The exact table type, the name of the process-wide value, the usage text, and which tiny sweep configuration serves as the
check (the plan's first task chooses it from the gate fixture).
