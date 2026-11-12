---
status: active
---

# v0.8 recursion once: implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Loops, self-calls and direct calls install on a kernel proof of the emitted code, through one generated simulation statement over a machine whose leaf instructions are rows of one table, with `loop`, the memory rows and the hand-written machine laws deleted.

**Architecture:** `tatic-wasm` splits into `machine.rs` (row schema, `Table`, `Ins`, stack shape, program encoding, meaning; backend-independent) and `wasm.rs` (the wasm table). The lowering emits every call as `Ins::Call(position)` with no `loop`, and the printer writes `return_call` by a fail-safe tail rule. Locals become a frame passed into every interpreter beside one opaque memory. A trusted statement builder (`machine/statement.rs`) states the module fixpoint over fuel with one law telescope; an untrusted generator (`machine/sim.rs`) proves it by walking the two sides' kernel terms with three rules (return, `choose`/congruence, call). `proof/gate.rs` returns a three-way verdict (`Accepted`, `Rejected`, `NotCovered`) and only `NotCovered` goes to `kernel_verify`.

**Tech Stack:** Rust 2024 workspace; `tatic-kernel` (Church-encoded CoC kernel, unchanged); `tatic-wasm`; wasmtime 42.0.1 (`Engine::default()`, `return_call` on by default); criterion `benches/execution.rs`; `~/.claude/runs/run.ps1` and `samply/icount.ps1` for recorded runs.

**Spec:** `docs/superpowers/specs/2026-11-10-v08-recursion-once-design.md` (status `active`; D1 to D5, O1 to O8, stages S0 to S4). The spec is the requirement: where a step says "per D3" or "per S2c", the spec's text is binding and is not repeated here. Its sources: the decision file `docs/decisions/2026-11-10-v08-shape-and-any-backend.md`; doc 15's sections 11 to 25 (index `docs/tier-cycle/README.md`); spike patches in `docs/superpowers/spikes/`. The spike code to start from is `2026-11-11-merge-call-rules-spike.patch` (w2) **alone** (it already contains the frame l3 patch); hunks are cited below as `w2:<path>` plus the function name, where `<path>` is relative to the crate's `src/` as the patch names it (`w2:wasm.rs`, `w2:wasm/sim.rs`, `w2:wasm/sim/tests.rs`, `w2:jit/lower_wat.rs`, `w2:jit/compile.rs`, `w2:proof/gate.rs`, `w2:proof/tests/gen_real.rs`).

**Where the work runs.** This plan file is untracked on `main` at writing; the user commits the approved plan on `main` before the worktree is made, so the branch carries it. All tasks run on a worktree branch `v08-recursion-once` off `main` (create it with superpowers:using-git-worktrees, at `../tatic-v08`). S2c steps 1 and 2 (T9) run on a sub-branch `v08-s2c-frame` off it and merge back only on the go/no-go's go. Never push, tag or merge to `main`; the user does that.

## Global Constraints

- The kernel does not change (no eta in conversion, no cumulativity). The generator passes continuations in the machine's own form and states lemma motives at the sort they land in (the law's leading numeral `d`, D4).
- Machine word width at the gate: `N = 64`. `Push(v)`/`const v` means `lit(n, (v as u64 as u128) & low_bits(n))` and prints `i64.const {v}`.
- Trusted: the rows, the printer and its tail rule, `Source::cps` and its source closure, `Call`'s meaning, the statement builder (module fixpoint, fuel quantification, law telescope, continuation relation; in `machine/statement.rs`, apart from the untrusted walk in `machine/sim.rs`), and the gate's checks that decide whether and which statement exists: the **shape check** (`machine.rs#shape_check` over the module's records: body from `[]` to `[word]`, no `Raw`, each `local.get` below its own function's width, every record's env `Params(0)`), the budget check, the registry pairing (S3). Untrusted: the walk; its value checks only fail early.
- Budget: `proof/gate.rs#MAX_GATE_TREE` stays 8192 nodes. A term's cost is its tree nodes plus a weight per `Call` site, counted on the **source** (every `Shape::SelfCall` and, from S3, `Shape::CombinatorCall` node that `classify` reads in the term and in the registry's callee terms), never from the emitted `Ins` list (D4's verdict: `NotCovered` is source-side only, or a mutant list padded with `Call`s would flip from `Rejected` to `NotCovered` and install through `kernel_verify`); over `MAX_GATE_TREE` is `NotCovered`. The weight starts at 0 and is fitted (T12) so a `Call`-bearing term at the budget takes as long as the relational `doubling(12)` (at most 0.57 s), every Goal 1 target under. The cap may be raised on purpose, never lowered below `doubling(12)`.
- The go/no-go (S2's only time gate): median of 5 `run.ps1 -Timed` runs of the relational `doubling(12)` build and check at most 0.57 s, which is 1.5 times the refl curve's 0.38 s re-measured in the same session. The linear-work guards keep their 2.05 bound.
- Module numbering (D3): a module of `n` callees puts callee `i` at position `i` (printed `$c{i}`) and the entry last at `n` (printed `$f`); `Ins::Call(j)` carries the position.
- Every printed function header keeps the four scratch declarations `$envtmp i32`, `$papenv i64`, `$diva i64`, `$divb i64`.
- Goldens: 34 in `crates/tatic/tests/golden/`. S0 keeps all 34 byte-identical; S2b regenerates exactly the 29 that hold a `loop` and keeps the 5 `rejects_*` byte-identical; from S2b on no golden changes.
- S0's dispatch cost: median instruction count within 0.5% of the post-deletion baseline, or the A/A spread if larger (ICOUNT.md, rotated arms).
- Deep builders run under `tatic_kernel::grow`; checking threads use `tatic_kernel::CHECK_STACK`, never a stack size literal.
- The guard loop, before every commit: `for g in size_check test_placement_check tour_check cite_check layout_check front_matter_check script_header_check stack_literal_check doc_index_check; do bash scripts/check/$g.sh || break; done`. `docs/TOUR.md` changes in the commit that adds, moves or deletes a module or a symbol it cites.
- Runs over a minute (scaling tests, golden sweep, icount, workspace suites) go through `powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind <kind> -Name v08-<name> -Affinity CFF -Command "<cmd>"`, from the worktree root (its `docs/runs.md` row lands on the branch). Below, `RUN(kind, name, cmd)` means that line. A timed run is `TRUN(kind, name, cmd)`: the same line with `-Timed -Affinity 100` (CPU 8, the timing core; CFF excludes CPUs 8 and 9, LONG_RUNS.md "CPU leases") in place of `-Affinity CFF`, and `cmd` is always a prebuilt exe copied out of `target` (`BUILD(<folder>-build, "cargo test -j 10 ... --no-run")`, `<folder>` the copy's folder, or the `cargo bench` form first, untimed), so no build runs under the lease. A test filter passed with `--exact` is the full libtest path (e.g. `proof::tests::gate::time_doubling_12`); a timed run whose output has no timing line is a failed run, not a result.
- **Builds and suites.** Every `cargo` command carries `-j 10`, written or not below (the 10 cores `CFF` leaves; LONG_RUNS.md "Cap concurrency"). A filtered test run on a warm build may stay bare. Whole-suite runs, `--all-targets` builds, `--no-run` exe builds and any build in a fresh scratch worktree go through `RUN` (memory cap, BelowNormal, a `docs/runs.md` row), from the worktree they build in. `SUITE(name)` below means `RUN(gate, name, "cargo test -j 10 -p tatic-wasm && cargo test -j 10 -p tatic --lib && cargo test -j 10 -p tatic --test golden_wat")`, and `BUILD(name, cmd)` means `RUN(probe, name, cmd)` for a build; their rows are staged with the task's commit (`docs/runs.md`).
- **Exe copies and the space in the profile path.** Copies live in `%LOCALAPPDATA%\claude-runs\tatic\<folder>\` (`C:\Users\Winston Li\...`), and `run.ps1` runs `-Command` through `cmd /s /c`, so a bare path splits at the space (LONG_RUNS.md "Paths with spaces"). No path ever appears in `-Command`: `EXE(folder, args)` below means `bash docs/runs/<T4's date>/scripts/v08-exe.sh <folder> <args>`, a script T4 creates (header comment in its first four lines) that resolves `"$LOCALAPPDATA/claude-runs/tatic/$1"`, quoted, fails unless that folder holds exactly one `.exe`, and runs it with the remaining arguments (none contains a space or a comma); its second form `v08-exe.sh icount <folder> <exeargs>` runs `powershell -NoProfile -File "$USERPROFILE/.claude/samply/icount.ps1" -Exe "<that exe>" -Runs 12 -Cpu 4 -ExeArgs <exeargs>` with every path quoted in bash. Copy with `mkdir -p "$LOCALAPPDATA/claude-runs/tatic/<folder>" && cp <exe> "$LOCALAPPDATA/claude-runs/tatic/<folder>/"`. In PowerShell (`icount.ps1 -Exe`), pass the path in a variable, never spliced into a string. After every recorded run, check that its `out.log` is non-empty and holds the expected line before reading the headline; an empty log is a launch failure, rerun, never counted.
- Findings go in doc 15 as new numbered section files (26 onwards) in its folder, each with its index line in `docs/tier-cycle/README.md`; `git add docs/tier-cycle` stages both. Cite sections by title, never by file name.
- Never let python read stdin (write `f.py`, run `python -P f.py < /dev/null`). Commit trailer `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. Never push or tag.
- A fallback the spec names is taken in its stage and recorded in the commit and, where it leaves a gap, in `PARKED.md`. A fallback that reopens frozen code, a stop condition, or a Goal 3 failure stops the builder for the user.

## Review Focus

1. **A tail self-call whose arguments permute the parameters** (`rec f a b = if a <= 0 then b else f (b - 1) a`). Arguments are on the stack when `return_call` runs, so the new frame must read the old one; a frame slot checked against the wrong source argument would accept a swap. Expect `Accepted` and agreement with eval. Pinned in T10 (`gate_accepts_a_permuting_tail_call`).
2. **Extreme literals as call arguments** (`i64::MIN`, `-1`, in a self-call's argument and a callee's). The masked `lit` must reach the callee's frame slot unchanged. Expect `Accepted`, and wasm agrees with eval at those inputs. Pinned in T10 (`gate_accepts_extreme_literals_in_call_arguments`).
3. **A self-call inside an `If` condition's operand** (`rec f n = if n <= 0 then 0 else if f (n - 1) < 3 then n else 0`). `cps` accepts it (a `SelfCall` is an operand), the printer must print `call` (the `If` follows), and the walk meets `choose` inside a call's continuation. Expect `Accepted`. Pinned in T10 (`gate_accepts_a_call_in_a_condition`).
4. **Tail and non-tail self-calls in one body** (`rec f n = if n <= 0 then 0 else if n < 2 then f (n - 1) else f (n - 1) + 1`). The printer must print `return_call` for the first and `call` for the second, and the proof covers the printed text only if `call; end` equals `return_call`. Expect `Accepted`, the WAT holding both forms, and eval agreement. Pinned in T6 (`tail_rule_prints_both_forms_in_one_body`) and T10 (`gate_accepts_mixed_tail_and_non_tail_calls`).
5. **A callee's own tail loop at depth 10^6** (a closed callee `$c0` that tail-calls itself 10^6 times, called once from `$f`). The deep-tail test covers only the entry; a callee printed with `call` for its tail call would trap. Expect `jit.apply` to return `n(n+1)/2` with `stats.compiled` 1. Pinned in T14 (`a_callee_tail_loop_runs_a_million_iterations`).

---

### Task 1: S0 baseline fixture

The fixture is committed alone, at `eba0891` behaviour (`git diff --stat eba0891 HEAD -- crates` is empty, so the branch base behaves as `eba0891`).

**Files:**
- Create: `crates/tatic/src/proof/tests/baseline.rs`
- Modify: `crates/tatic/src/proof/tests.rs` (`mod baseline;`), this plan's front matter (`status: active`)

**Interfaces:**
- Consumes: `support::samples::corpus()` (census 1-23); the `testing/test_corpus.rs` builders of census 24-38, in the order of the census list in doc 15's section "v0.7's first steps: the census and the emit spike"; `JitEngine::{new, apply, stats}`; `compile::{compile_specialised, tree_size}`; `shape::peel`.
- Produces (later tasks add tables to this file):
  - `pub(super) struct BaseRow { name: &'static str, installs: bool, compiled: u64, specialised: u64, tree: u64 }`
  - `pub(super) const BASELINE: &[BaseRow]` (a literal, one row per census term)
  - `pub(super) const HELD_OUT: &[&str] = &[];` (T8 names its two rows here; Goal 5's one exception lives in `baseline_fixture_matches` alone: a `HELD_OUT` row's `installs` may go from false to true, never back, and when it changed, `compiled` and `specialised` are not compared)
  - `pub(super) fn census() -> Vec<(&'static str, TermStore, Hash)>` (corpus then builders)
  - `fn measure(name, s, h) -> BaseRow`: one `JitEngine::apply(&s, h, &vec![5; arity])` with `arity` from `peel`, ignoring an `Err`; `installs = stats.compiled == 1`; `tree = tree_size` of the specialised term from `compile_specialised` (`h` when `specialised` is `None` or nothing compiles).

- [ ] **Step 1: Check the base.** Run: `git diff --stat eba0891 HEAD -- crates`. Expected: empty output. Set this plan's front matter to `status: active`.
- [ ] **Step 2: Write the failing test.**
  ```rust
  #[test] fn baseline_fixture_matches()      // for every census() term: measure(..) == the BASELINE row of that name
                                             // (HELD_OUT rows: the exception above); every census name has exactly
                                             // one row and every row a census name
  #[test] #[ignore] fn print_baseline_rows() // prints measure(..) of every census term as a Rust literal row
  ```
  With `BASELINE` empty. Run: `cargo test -p tatic --lib baseline_fixture_matches`. Expected: FAIL, "no row for factorial".
- [ ] **Step 3: Fill the table.** Run `cargo test -p tatic --lib print_baseline_rows -- --ignored --nocapture` and paste its output as `BASELINE`. Read every row: factorial, both sum loops and `inc` install; a term that does not compile has `compiled: 0`.
- [ ] **Step 4: Run.** Run: `cargo test -p tatic --lib baseline_fixture_matches`. Expected: PASS.
- [ ] **Step 5: Guard loop, commit.**
  ```bash
  git add crates/tatic/src/proof/tests.rs crates/tatic/src/proof/tests/baseline.rs docs/superpowers/plans/2026-11-11-v08-recursion-once.md
  git commit -m "proof: v0.8 baseline fixture, one row per census term at eba0891 behaviour"
  ```

### Task 2: S0 memo guard moves to the kernel; `countdown` and `Dup` go

**Files:**
- Create: `crates/tatic-kernel/src/tests/memo.rs` gains the test (the file exists; add to it), `docs/runs/<date>/patches/v08-memo-off.patch`
- Modify: `crates/tatic-wasm/src/wasm.rs` (delete `Ins::Dup`, its `shape`, `seq_step` and `interp` arms and the `dup` constructor; `ifp`'s constructor index follows), `crates/tatic-wasm/src/wasm/laws.rs` (delete `countdown`, `countdown_law`, their `run_wasm_checks` lines, `countdown_invariant_is_not_exponential`), `crates/tatic-wasm/src/print.rs` (the `Dup` panic arm), `crates/tatic-wasm/src/ops.rs` (`LtU`'s doc: it now serves the `LtS`-for-`LtU` control only), `docs/TOUR.md` if it names any of these

**Interfaces:**
- Consumes: `tatic_kernel::{def_eq, work}` and the term builders `tests/memo.rs` already uses; `reduce.rs#conv`'s `EQUAL` memo.
- Produces: `#[test] fn conv_memo_keeps_a_shared_tail_case_tree_linear()` in `tatic-kernel/src/tests/memo.rs`.

- [ ] **Step 1: Write the guard.** A case tree of depth `d` whose every path ends in the same continuation-applied borrow-chain tail (the shape `reduce.rs#conv`'s doc describes: two equal but distinct subterms under a shared-tail case tree). Assert `def_eq` holds at `d = 16` and that `tatic_kernel::work()` grows at most 2.05x per step from `d = 14` to `d = 16`; also assert the `d = 16` check takes under 2 s.
  Run: `cargo test -p tatic-kernel --lib conv_memo_keeps_a_shared_tail_case_tree_linear`. Expected: PASS.
- [ ] **Step 2: Show it red without the memo.** Comment out the `EQUAL` lookup in `conv`, then `RUN(probe, memo-off, "cargo test -j 10 -p tatic-kernel --lib conv_memo_keeps_a_shared_tail_case_tree_linear")`. Expected: exit non-zero on the growth assertion (2^d growth). Save `git diff crates/tatic-kernel` as `docs/runs/<date>/patches/v08-memo-off.patch`, then `git checkout crates/tatic-kernel/src/reduce.rs`.
  **Fork** (spec S0's "Done when" alternative): if it stays green with the memo off, no small tree reaches the memo: delete the new test, and add a `PARKED.md` entry saying the guard goes and why ("conv pair-memo guard": `countdown_invariant_is_not_exponential` is deleted with `countdown`, no small case tree is exponential without the memo; trigger: a regression in `conv`; evidence: the run id; status `decided against`). Step 3 runs the same either way.
- [ ] **Step 3: Delete** `countdown`, `countdown_law`, their `run_wasm_checks` lines, `countdown_invariant_is_not_exponential` and `Dup` everywhere (`rg -n 'Dup|countdown' crates/tatic-wasm crates/tatic`; `universal.rs`'s source-level `countdown` test is unrelated and stays).
  Run: `SUITE(t2-suite)`. Expected: exit 0, `git status --short crates/tatic/tests/golden` empty.
- [ ] **Step 4: Guard loop, commit** (this commit is T4's icount arm A; T4 finds it by its subject).
  ```bash
  git add crates/tatic-kernel/src/tests/memo.rs crates/tatic-wasm docs/runs docs/runs.md docs/TOUR.md PARKED.md
  git commit -m "kernel: conv pair-memo guard on a shared-tail case tree; wasm: countdown, its law and Dup deleted (D1)"
  # on the fork the subject's first clause reads "kernel: conv pair-memo guard parked"; T4 greps '^kernel: conv pair-memo guard' either way
  ```

### Task 3: S0 the row schema, the table, `machine.rs`, `Ins::Row`, and `&Table` threaded

S0 lands as one change (spec S0: "Ins leaf variants become Ins::Row"): `wasm.rs` splits, the machine moves to `machine.rs`, table-driven, `wasm.rs` keeps the wasm table, and `Ins::Row` replaces the leaf variants in the same commit, so no bridge from `Op` to rows exists at any commit and each test is ported once.

**Files:**
- Create: `crates/tatic-wasm/src/machine.rs` (moved from `wasm.rs`: `choose`, `K`, `Ins`, `shape`/`out_stack`/`well_formed`, `prod`, `mkpair`, `nat2`, `nat2_lit`, the machine struct and its `impl` through `meaning`, `append`, `ifp`, `spec`, `good_nat`, `good`, and their tests)
- Modify: `crates/tatic-wasm/src/wasm.rs` (only `pub fn table() -> Table` and its tests), `crates/tatic-wasm/src/ops.rs` (the `Op` enum goes; the file holds the rows' meaning builders and lines), `crates/tatic-wasm/src/lib.rs` (`pub mod machine;`), `crates/tatic-wasm/src/wasm/laws.rs` (moves to `crates/tatic-wasm/src/machine/laws.rs` with `git mv`; it takes a `&Table`), `crates/tatic-wasm/src/print.rs`, `crates/tatic/src/lang/term.rs` (`PrimOp::name`), `crates/tatic/src/jit/shape.rs` (`wasm_table`, `op_of` deleted), `crates/tatic/src/jit/lower_wat.rs`, `crates/tatic/src/jit/compile.rs`, `crates/tatic/src/jit/ir.rs`, `crates/tatic/src/proof/universal.rs`, `crates/tatic/src/proof/gate.rs`, `crates/tatic/src/jit.rs`, `crates/tatic/src/jit/op_table_tests.rs`, `crates/tatic/src/jit/tests.rs` (`an_operand_if_installs_through_the_chain`'s `in_fragment` call gains `shape::wasm_table()`), `crates/tatic/src/testing/ins_mutate.rs`, `crates/tatic/src/proof/tests/gate.rs`, `docs/TOUR.md`

**Interfaces:**
- Produces, in `tatic_wasm::machine`:
  - `pub enum Class { Const, Word, Bit }` (`Copy, Debug, PartialEq, Eq`): `Const` is 0 to 1 with a word result, `Word` 2 to 1 word-valued, `Bit` 2 to 1 bit-valued. `pub fn pops(self) -> usize` (0, 2, 2) and `pub fn kind(self) -> K` (`W`, `W`, `B`).
  - `pub struct Row { pub name: &'static str, pub class: Class, pub meaning: fn(&mut Cx, &Machine, i64) -> Expr, pub line: fn(i64) -> String }`. `meaning(c, m, operand)` is the constructor's operand: for `Const` the word (a numeral today; `Fr -> V` from T9), for `Word`/`Bit` the closed circuit.
  - `pub struct Table { rows: Vec<Row> }` with `pub fn new(rows: Vec<Row>) -> Table` (panics on a duplicate name) and `pub fn row(&self, name: &str) -> Option<&Row>`.
  - `pub struct Machine<'t> { pub n: usize, pub table: &'t Table }` (`Clone, Copy`), replacing `wasm::Wasm`; every method keeps its name and signature.
  - `pub enum Ins { Row { name: &'static str, operand: i64 }, LocalGet(u32), If(Vec<Ins>, Vec<Ins>), Loop(Vec<Ins>), Br(usize), Store, Load, Raw(String) }`. A 2-to-1 row carries operand 0; `shape` rejects a nonzero operand on a `Word`/`Bit` row and an `Ins::Row` whose name the table lacks (both `Err`, so `well_formed` is false).
  - Constructor order, derived in one private fn `ctor_list() -> Vec<Ctor>`: the leaf classes `Const, Word, Bit` (one constructor per class, as today's push/bin/cmp), then the structural classes `If, Loop, Store, Load` (deleted in T7 and T9 as the spec says). `ctor_ty`'s leaf arms, `interp`'s leaf entries, `seq_step`'s constructor indices, `ifp`'s index and the constructor count are read from it; no index literal remains. `seq_step` builds an `Ins::Row`'s constructor from its row's class, with `meaning(row, operand)` as the operand.
  - `pub fn out_stack(table: &Table, code: &[Ins], st: Vec<K>) -> Option<Vec<K>>`, `pub fn well_formed(table: &Table, code: &[Ins], st: &[K]) -> bool` (a leaf's stack effect from its row's class).
  - `pub fn print_body(table: &Table, code: &[Ins], depth: usize, out: &mut String)`: a row prints `(row.line)(operand)`; the panic arms for machine-only variants stay.
- Produces, in `tatic_wasm::wasm`: `pub fn table() -> Table` with rows `const` (`Const`, `i64.const {v}`), `add`, `sub`, `mul` (`Word`), `lt` (`i64.lt_s`), `le` (`i64.le_s`), `eq`, `lt_u` (`Bit`); meanings `constant_n(<circuit>, m.n)` as `Op::term` builds them today.
- Produces, in tatic: `impl PrimOp { pub fn name(self) -> &'static str }` (`Add` "add", `Sub` "sub", `Mul` "mul", `Lt` "lt", `Le` "le", `Eq` "eq", `Div` "div", `Mod` "mod"); `pub fn wasm_table() -> &'static Table` in `jit/shape.rs` (a `OnceLock`); `shape::is_comparison(op) = wasm_table().row(op.name()).is_some_and(|r| r.class == Class::Bit)`; the lowering emits `Ins::Row { name: op.name(), operand: 0 }` after checking the row's class (the `expect` messages name `wasm_table`), and `Node::Lit(v)` emits `Ins::Row { name: "const", operand: v }`; `gate(table: &Table, store, h, arity, code)`, `gate_with(table, ..)`, `statement(table, ..)`, `in_fragment(table, ..)`, and `Source { table, store, qs, r }`. `prove_install` passes `shape::wasm_table()`.
- Deleted: `Ins::Push`, `Ins::Op`, the `Op` enum and `Op::{term, mnemonic, kind}`, `shape::op_of`.

- [ ] **Step 1: Write the failing tests.**
  ```rust
  // wasm.rs tests
  #[test] fn wasm_rows_are_closed_and_typed()   // every row of table() at n = 8: a Word row's meaning infers V -> V -> V,
                                                // a Bit row's V -> V -> Bv_1, a Const row's (operand 3) V; replaces
                                                // ops.rs#op_rows_are_closed_and_typed
  // machine.rs tests
  #[test] fn well_formed_rejects_unknown_rows_and_operands_on_binary_rows()
  //   from []: [Row{"nope",0}] false; [const 1, const 2, Row{"add", 7}] false; [const 1, const 2, Row{"add", 0}] true
  // tatic's jit/op_table_tests.rs
  #[test] fn every_prim_op_with_a_row_names_it() // for each PrimOp p, wasm_table().row(p.name()) is Some exactly for
                                                // the six non-Div/Mod ops, and its class is Bit exactly when
                                                // shape::is_comparison(p)
  ```
  Port, once, to `Ins::Row`: `well_formed_rejects_raw_underflow_bad_br_and_mismatched_arms`, `local_get_reads_the_frame`, `print_body_shapes`, `gate_rejects_mutations`' mutators (mutations name rows: `add` to `sub`, `lt` to `lt_u`) and `op_table_tests`.
  Run: `cargo test -p tatic-wasm wasm_rows_are_closed_and_typed`. Expected: compile error (`Table` not found).
- [ ] **Step 2: Split, derive and migrate.** `git mv` first so history follows the machine (`git mv crates/tatic-wasm/src/wasm.rs crates/tatic-wasm/src/machine.rs`, then create the new `wasm.rs`); then derive and migrate as in Interfaces. Then `rg -n 'op_of|Ins::Push|Ins::Op\b|ops::Op\b|(^|[^A-Za-z])Op::' crates/tatic-wasm crates/tatic` is empty (the anchor keeps `PrimOp::` out, and the scope keeps out `church-bv`'s own unrelated `enum Op`); the compile is the full check, since the `Op` type is gone.
- [ ] **Step 3: Run.** Run: `SUITE(t3-suite)`. Expected: exit 0; the 34 goldens byte-identical (`git status --short crates/tatic/tests/golden` empty).
- [ ] **Step 4: Guard loop** (TOUR: `machine.rs` for the old `wasm.rs` line; `Row`, `Table`, `Class`, `Ins::Row` in the glossary; `op_of` removed), **commit.**
  ```bash
  git add crates/tatic-wasm crates/tatic/src docs/TOUR.md docs/runs.md
  git commit -m "tatic-wasm: machine.rs over a table of rows (three leaf classes, derived constructor order); Ins::Row { name, operand } replaces the leaf variants; wasm.rs is the wasm table; PrimOp::name pairs source and row; gate takes &Table; op_of deleted"
  ```

### Task 4: S0's dispatch check

Measurement only: no code under `crates/` changes unless the check misses (then the lookup fix below is its own commit, with its pathspecs, before the rerun).

**Files:**
- Create: `docs/runs/<date>/scripts/v08-exe.sh` (Global Constraints' `EXE`; every later recorded exe run uses it)
- Modify: `docs/runs.md` (rows)

- [ ] **Step 1: S0's dispatch check (Done when).** Build both arms' test exes (`BUILD(s0-build-<arm>, "cargo test -j 10 -p tatic-wasm --lib --no-run && cargo test -j 10 -p tatic --lib --no-run")`, each from its own worktree) at T2's commit (arm A, `git log --grep '^kernel: conv pair-memo guard' --format=%h -1`, in a scratch worktree) and at T3's (arm B); copy each exe into its own folder (`v08-s0-<crate>-<arm>`, the `cp` line in Global Constraints). First write `docs/runs/<date>/scripts/v08-exe.sh` (both forms, Global Constraints) and check it: `bash docs/runs/<date>/scripts/v08-exe.sh no-such-folder` exits non-zero naming the folder. Count with the script's icount form, `v08-exe.sh icount <folder> <filter>,--ignored,--exact`, for `machine::laws::wasm_scaling` (`wasm::laws::wasm_scaling` in arm A), and without `--ignored` for `proof::tests::gate::gate_check_work_is_linear_in_the_tree` and `proof::tests::gate::gate_build_work_is_linear_in_the_tree` (full paths: `--exact` matches the whole path); check each count is workload-sized, not start-up-sized (ICOUNT.md); rotate A, B, B, A over batches of at least 4, as ICOUNT.md says. Record a row per batch in `docs/runs.md` (each batch is `RUN(probe, s0-icount-<exe>-<arm>, "bash docs/runs/<date>/scripts/v08-exe.sh icount <folder> <exeargs>")`).
  Expected: B's median within 0.5% of A's (or of the A/A spread if larger). If above, profile the lookup (a `HashMap` by name in `Table` is the first fix, a T3 code change in its own commit) and rerun before committing; the numbers go in T13's findings.
- [ ] **Step 2: Guard loop, commit.**
  ```bash
  git add docs/runs.md docs/runs/*/scripts/v08-exe.sh
  git commit -m "runs: S0's dispatch check (icount A/B, rows by name against the leaf variants)"
  ```

### Task 5: S2a the empty-`rest` call probe (O8); S2b bench baseline

Nothing on the branch changes but the probe's patch and the run rows (this probe's and S2b's bench baseline, which must exist before T6 changes the lowering). On a probe failure, stop and report: nothing has been deleted yet.

**Files:**
- Create: `docs/superpowers/spikes/2026-11-1x-empty-rest-call-spike.patch` (the date of the run)
- Modify: `docs/runs.md` (the probe's row and the bench's)

**Interfaces:**
- Consumes: the w2 patch, applied to a scratch worktree at `fb2a284` from the branch worktree's copy by absolute path (the patch is not in `fb2a284`'s tree: it arrived in `bfdb24a`): `git worktree add ../tatic-s2a fb2a284 && git -C ../tatic-s2a apply "$(pwd)/docs/superpowers/spikes/2026-11-11-merge-call-rules-spike.patch"`, run from the branch worktree's root. The patch creates three files (`wasm/sim.rs`, `wasm/sim/tests.rs`, `proof/tests/gen_real.rs`).
- Produces: the verdict list (each target proved, each control rejected) and the run id, for T13's findings; the bench baseline's run id.

- [ ] **Step 1: Edit the spike machine.** In `w2:wasm.rs`, delete `Ins::ReturnCall`, its constructor (index 11), its `shape` arm and its interpreter, and `Hooks::ret`; a tail call becomes `Ins::Call` followed by nothing, whose `rest` is the empty program (its continuation is the activation's own, up to `rel`). In `w2:jit/lower_wat.rs` the `SelfCall` arm emits `call` for both tails. In `w2:wasm/sim.rs` the call rule applies the callee law with the walk's own `km`, `ks`, `rel` when the continuation reached is the activation's (the `cont_rel` walk proves it up to `rel`); `check_code` drops the `ReturnCall` clause.
- [ ] **Step 2: Add the targets and controls** to `w2:proof/tests/gen_real.rs`'s `gen_real` tests: `capturing_closure_loop`, `partial_application_loop`, a tail loop stepping by 2 (`rec f n acc = if n <= 1 then acc else f (n - 2) (acc + n)`), term 13 and term 34 (each with its callee call last). Controls on a sum loop: arguments swapped, the call dropped (the arm answers `acc`), and the call rule given a wrong `km`, a wrong `ks` and a wrong `rel` (three test-only substitutions inside the walk); the wrong-`km` control also on term 13's callee call.
- [ ] **Step 3: Run.** `RUN(probe, s2a-empty-rest, "cargo test -j 10 -p tatic --lib gen_real -- --nocapture")` from `../tatic-s2a` (the row lands there; copy it to the branch's `docs/runs.md`). Expected: every target proves through `tatic_kernel::check`; every control fails with a named reason or a kernel rejection. **Stop** on any other outcome (O8's fallback reverses a decision).
- [ ] **Step 4: Keep the patch, remove the worktree.** The patch's new files are untracked after `git apply`, so stage them first: `git -C ../tatic-s2a add -A crates && git -C ../tatic-s2a diff --cached fb2a284 -- crates > docs/superpowers/spikes/<name>.patch`; check it holds `new file mode` for the three new files; `git worktree remove --force ../tatic-s2a`.
- [ ] **Step 5: S2b bench before** (on the branch, unchanged lowering). Build untimed: `BUILD(s2b-bench-build, "cargo bench -j 10 -p tatic --bench execution --no-run")`; copy the bench exe its log names into folder `v08-bench-before` (the `cp` line in Global Constraints). Then `TRUN(bench, s2b-bench-before, "EXE(v08-bench-before, --bench gcd_tail_recursion_to_loop)")` (`EXE(..)` written out as its `bash ... v08-exe.sh` line, here and below) and the same for `capturing_closure_loop` (`s2b-bench-before-ccl`). Expected: exit 0; each `out.log` non-empty and holding criterion's `time:` line; note the medians.
- [ ] **Step 6: Commit.**
  ```bash
  git add docs/superpowers/spikes docs/runs.md
  git commit -m "docs: S2a probe, a tail call as Call with an empty rest proves every target and rejects every control (O8 settled); S2b bench baseline (loop lowering)"
  ```

### Task 6: S2b every call emitted as `Ins::Call`, the entry record, the tail rule

**Files:**
- Create: `crates/tatic/src/jit/tail_rule_tests.rs` (`#[cfg(test)] mod tail_rule_tests;` in `jit.rs`)
- Modify: `crates/tatic-wasm/src/machine.rs` (`Ins::Call`, `EnvAccess`, `Entry`, shape's call arity), `crates/tatic-wasm/src/print.rs` (header from the record, labels by position, the tail rule), `crates/tatic/src/jit/lower_wat.rs`, `crates/tatic/src/jit/compile.rs`, `crates/tatic/src/jit/ir.rs`, `crates/tatic/src/jit/compile/tests.rs`, `crates/tatic/src/testing/ir_fuzz.rs`, `crates/tatic/src/verify/decompile/tests.rs`, `crates/tatic/src/jit/tests.rs` (its three `prove_install` calls, in `the_installation_proof_is_about_the_specialised_term` and `the_gates_verdict_is_final_for_fragment_terms`, and that test's `mutate` call take `&frag.entry().code`), `crates/tatic/src/proof/tests/gate.rs`, `crates/tatic/src/proof/tests/baseline.rs`, `crates/tatic/src/proof.rs`, `crates/tatic/src/proof/universal.rs` (headers only), `crates/tatic/src/jit.rs` (`try_install` passes `&frag.entry().code` to `prove_install`, whose `code: &[Ins]` parameter stays; the `kernel_verify` doc of Step 2), `crates/tatic/src/proof/gate.rs` (`gate`'s `well_formed` call gains `arities` `&[]`: no `in_fragment` term holds a `Call`), the 29 goldens, `docs/TOUR.md`

**Interfaces:**
- Consumes: T3's `Ins`, `Table`, `print_body`; the IR's `Node::{SelfCall, CallKnown}`; `compile.rs#build`'s registry.
- Produces:
  - In `machine.rs`: `Ins::Call(usize)` (a module position); `pub enum EnvAccess { Params(usize), Pointer }` (`Params(k)` prints `$e0..$e{k-1}`, `Pointer` prints `$env i32`); `pub struct Entry { pub arity: usize, pub env: EnvAccess, pub code: Vec<Ins> }` (`Clone, Debug, PartialEq, Eq`); `pub fn out_stack(table: &Table, code: &[Ins], st: Vec<K>, arities: &[Option<usize>]) -> Option<Vec<K>>` and `pub fn well_formed(table: &Table, code: &[Ins], st: &[K], arities: &[Option<usize>]) -> bool` (one code list; T10's `shape_check` over records calls it), where `Call(j)` pops `arities[j]` words and pushes one, and a `j` out of range or `None` is `Err`. `seq_step` on `Call` is `unreachable!("Call has no meaning before S2c")`: no code holding one reaches the gate (`in_fragment` admits no `App`).
  - In `print.rs`: `pub fn print_func(table: &Table, pos: usize, entry_pos: usize, e: &Entry, out: &mut String)` (header `  (func $c{pos}` or `  (func $f`, then the env access's params, `$p{i}` params, `(result i64)`, the four scratch declarations, the body at depth 4, `  )`); `pub fn print_body(table: &Table, code: &[Ins], depth: usize, tail: bool, entry_pos: usize, out: &mut String)`, where a `Call(j)` prints `return_call <label j>` when `tail` holds and it is the last instruction of `code`, `call <label j>` otherwise; an `If` passes `tail && it is last` to both arms; `print_func` passes `tail = true`.
  - In `compile.rs`: `Item::Func { pos: usize, entry: Entry }` (no `name`, no `header`); `CompiledFragment { arity, module, needs_hp_reset, entry_pos: usize }` with `entry_pos` = the combinator count; `pub fn entry(&self) -> &Entry` (the `Func` at `entry_pos`); `pub fn records(&self) -> Vec<Option<&Entry>>` (index = position, `None` for a partial-application wrapper); `wat()` calls `print_func`.
  - In `lower_wat.rs`: `function(&mut self, pos: usize, f: &Func, env: EnvAccess) -> Item`; `node`'s `SelfCall { args }` (one arm) and every `CallKnown { f, .. }` emit the env words, the arguments, then `Ins::Call(pos)` (a `CallKnown` target is always `Lifted`: `ir.rs#lifted` rejects a `Pap` target, so no `CallKnown` keeps a `Raw` call line); a `Pap` wrapper stays an `Item::Text` with no record, and `call_indirect` and `dynamic_apply` stay `Raw`; `direct_only` drops its `env_len > 0` filter, so a closed direct callee is `Params(0)` with no `$env`, and its callers push no `i32.const 0`; the entry is `Params(0)`. Deleted: `EnvAccess::None`, the `Loop` wrapper, the tail staging, the `$t{i}` declarations.
  - In `ir.rs`: `Node::SelfCall { args: Vec<Node> }`; the "outside tail position" check and its tests go, as do the `tail` arguments in `compile.rs`, `testing/ir_fuzz.rs` and `verify/decompile/tests.rs`.

- [ ] **Step 1: Write the failing tests.**
  ```rust
  // jit/tail_rule_tests.rs
  #[test] fn tail_rule_matches_call_everywhere_under_wasmtime()
  //   every well-formed entry body over the alphabet {const 1, local.get 0, add, Call(0), If(lt)} up to 4 instructions
  //   (If arms up to 2) that ends on [W]: printed once with print_func (tail rule) and once with every Call as `call`
  //   (print_body with tail = false); both run under wasmtime at p0 in {0, 3} beside a callee $c0 = \x. x + 100;
  //   the two answers are equal. A wrong rule shows: return_call before `add` skips the add.
  #[test] fn tail_rule_prints_both_forms_in_one_body()
  //   rec f n = if n <= 0 then 0 else if n < 2 then f (n - 1) else f (n - 1) + 1: the WAT holds one `return_call $f`
  //   and one `call $f`, and jit.apply agrees with eval at n in {0, 1, 5}            (Review Focus 4)
  // jit/tests.rs
  #[test] fn a_tail_loop_of_a_million_iterations_installs_and_runs()
  //   rec f n acc = if n <= 0 then acc else f (n - 1) (acc + n): jit.apply at (10^6, 0) = n(n+1)/2, stats.compiled 1;
  //   the same WAT with `return_call` replaced by `call` traps under wasmtime
  #[test] fn every_function_header_declares_the_scratch_locals() // every Func of every census term's wat()
  #[test] fn calls_go_to_kernel_verify_until_the_gate_covers_them()
  //   factorial and capturing_closure_loop (specialised): in_fragment false, try_install gives Compiled
  // proof/tests/baseline.rs
  #[test] fn membership_matches()
  //   for the Goal 1 targets (capturing_closure_loop, partial_application_loop, factorial,
  //   redundant_arithmetic_recursion, fib; stage S2c) and Goal 2 targets (twice_inc_5, let_bound_factorial_10,
  //   tail_recursive_loop_with_pap_producing_root_self_call_arg; stage S3): a literal MEMBERSHIP table of
  //   (name, no_raw, under_cap, single_entry, stage) equals the measured one, where no_raw is "no Raw at any depth in
  //   any record of the specialised fragment", under_cap is tree_size <= MAX_GATE_TREE, single_entry is records()
  //   holding only the entry
  ```
  Change `baseline_fixture_matches` to compare `installs`, `compiled`, `specialised` only (the spec: after S2b; the `HELD_OUT` exception unchanged). Change the tests that name the wrapper (`fragment_bodies_contain_no_raw`, `gate_rejects_mutations` and `measure_gate_costs` in `proof/tests/gate.rs`): the body is the code itself; "`Raw` appended inside the `Loop`" becomes "appended to the body".
  Run: `cargo test -p tatic --lib tail_rule`. Expected: compile error (`print_func` not found).
- [ ] **Step 2: Implement** the Interfaces. Model provers' headers (`proof.rs` module doc, `proof/universal.rs`, `jit.rs`'s `kernel_verify` doc): "the compiled code loops" becomes "the model states the IR's tail self-call as `loop`/`br`, which stands for the emitted `return_call`".
- [ ] **Step 3: Regenerate the goldens.** Run `cargo test -j 10 -p tatic --test golden_wat` (expected: 3 tests fail, the three golden comparisons, whose assertion messages together name the 29 changed files; `the_redundant_arithmetic_benchmark_still_evaluates` passes), then `UPDATE_GOLDEN=1 cargo test -j 10 -p tatic --test golden_wat`. Expected: `git status --short crates/tatic/tests/golden` lists exactly the 29 non-`rejects_*` files; read three diffs (factorial, a sum loop, `twice_inc_5`): no `loop`, `return_call $f` at tail calls, `call $c0` with no `i32.const 0` before it.
- [ ] **Step 4: Fill `MEMBERSHIP`** from a print helper as in T1. **Checkpoint:** if any Goal 1 target has `no_raw`, `under_cap` or `single_entry` false, or all three Goal 2 targets have `no_raw` false, **stop and report**. Each Goal 2 target excluded alone gets a `PARKED.md` entry (what, why parked: its specialised code holds the `Raw` line named, trigger: the rung that removes it, evidence: this test, status `parked`).
- [ ] **Step 5: Run.** `RUN(gate, s2b-suite, "cargo test -j 10 -p tatic && cargo test -j 10 -p tatic-wasm")` (the lib suite includes `ir_fuzz`; `tests/compile_fuzz.rs` is the differential compile fuzz). Expected: exit 0.
- [ ] **Step 6: Guard loop** (TOUR: `Entry`, `EnvAccess` in `machine.rs`; `Item::Func`'s fields; the tail rule in the data flow), **commit.**
  ```bash
  git add crates/tatic-wasm crates/tatic docs/TOUR.md PARKED.md docs/runs.md
  git commit -m "jit: every call is Ins::Call(position) with no loop; the entry record moves to tatic-wasm; the printer derives headers and prints return_call by its tail rule (D1, D3)"
  ```

### Task 7: S2b the loop machinery goes; the bench after

**Files:**
- Modify: `crates/tatic-wasm/src/machine.rs` (`Ins::Loop`, `Ins::Br`, the `loops` stack in `shape`, the `labels` of `seq`), `crates/tatic-wasm/src/print.rs` (the `Loop`/`Br` arms), `crates/tatic/src/proof/gate.rs` (`gate_with`, `strip_loop`), `crates/tatic/src/testing/ins_mutate.rs` (its `Loop` arm), `crates/tatic/src/proof/tests/gate.rs`, `docs/TOUR.md`

**Interfaces:**
- Produces: `Ins { Row, LocalGet, If, Store, Load, Call, Raw }`; `gate(table, store, h, arity, code)` calls `statement(table, store, h, arity, code, 1)` directly. Stays, inert, until T9: the `Loop` structural constructor and its interpreter (`loop_law` uses them), `fuel`, fuel 1, `loop_law`, `timeout`, `Machine::good`, the refl `statement`.

- [ ] **Step 1: Delete** as listed. `well_formed_rejects_raw_underflow_bad_br_and_mismatched_arms` loses its `Loop`/`Br` cases (renamed `well_formed_rejects_raw_underflow_and_mismatched_arms`).
  Run: `BUILD(t7-build, "cargo build -j 10 -p tatic --all-targets")`, then `grep -cE "^(warning|error)"` over its `out.log` and `err.log`. Expected: exit 0 and 0 matches.
- [ ] **Step 2: Run.** `SUITE(t7-suite)`. Expected: exit 0, goldens unchanged since T6.
- [ ] **Step 3: Bench after.** As T5 Step 5 (a fresh `--no-run` build copied to `v08-bench-after`), `TRUN(bench, s2b-bench-after, ...)` and `s2b-bench-after-ccl`. Expected: exit 0; a slowdown is a finding for T13, not a gate.
- [ ] **Step 4: Guard loop, commit.**
  ```bash
  git add crates/tatic-wasm crates/tatic/src docs/TOUR.md docs/runs.md
  git commit -m "tatic-wasm: Ins::Loop, Ins::Br, the loop stack, gate_with and strip_loop deleted (D1); S2b bench after"
  ```

### Task 8: Held-out terms (before S2c step 1)

A subagent (Sonnet) is given only this brief: "`cps` takes a closed `Rec` or `Abs^k` term whose body is built from parameters, integer literals, `+`, `-`, `*`, an `if` on `<`, `<=` or `==` of such operands in tail position (its arms again such bodies), and saturated self-calls in any operand or tail position; no closures, no division, no other functions. Write two such terms that are not factorial, fib, a sum loop or `redundant_arithmetic_recursion`: a two-parameter non-tail recursion and a tail loop of another step shape. Each under 200 nodes." It does not see the generator, the spike patches or the spec's other sections.

**Files:**
- Modify: `crates/tatic/src/testing/test_corpus.rs` (`pub(crate) fn held_out_a(s)`, `held_out_b(s)`), `crates/tatic/src/proof/tests/baseline.rs` (two rows appended to `BASELINE`, measured at `eba0891`)

- [ ] **Step 1: Dispatch the subagent** with the brief above (and the python rule). Check its terms: each parses, has no `Div`/`Mod`, closures or other heads, and compiles with no `Raw` in `records()`.
- [ ] **Step 2: Measure at `eba0891`** in a scratch worktree. `eba0891` has no `baseline.rs`, so bring T1's version in (it uses only APIs that exist there; T1's commit changed nothing else under `crates/`): `git worktree add ../tatic-ho eba0891`, then `git -C ../tatic-ho checkout $(git log --grep '^proof: v0.8 baseline fixture' --format=%h -1) -- crates/tatic/src/proof/tests/baseline.rs crates/tatic/src/proof/tests.rs`. Add the two builders to `../tatic-ho`'s `test_corpus.rs` and to its `census()` after census 38, run `BUILD(t8-held-out-rows, "cargo test -j 10 -p tatic --lib print_baseline_rows -- --ignored --nocapture")` from `../tatic-ho` (copy its row to the branch's `docs/runs.md`), and take the two new rows from its output. Remove the worktree (`git worktree remove --force ../tatic-ho`). Here: append the two rows to `BASELINE`, add their builders to `census()` after census 38, and set `HELD_OUT = &["held_out_a", "held_out_b"]`.
- [ ] **Step 3: Run.** `cargo test -j 10 -p tatic --lib baseline`. Expected: PASS.
- [ ] **Step 4: Commit.**
  ```bash
  git add crates/tatic/src/testing/test_corpus.rs crates/tatic/src/proof/tests/baseline.rs docs/runs.md
  git commit -m "test: two held-out terms written without sight of the generator, with their eba0891 baseline rows"
  ```

### Task 9: S2c steps 1 and 2 (sub-branch): the frame, the memory, the one statement on straight-line terms, the go/no-go

Run on `git switch -c v08-s2c-frame`. Commits between Step 3 and Step 6 may be red; the merge is green.

**Files:**
- Create: `crates/tatic-wasm/src/machine/statement.rs`, `crates/tatic-wasm/src/machine/sim.rs`, `crates/tatic-wasm/src/machine/sim/tests.rs` (w2's layout; the mini `Src` lives there)
- Modify: `crates/tatic-wasm/src/machine.rs`, `crates/tatic-wasm/src/wasm.rs`, `crates/tatic-wasm/src/ops.rs`, `crates/tatic-wasm/src/print.rs`, `crates/tatic/src/proof/gate.rs`, `crates/tatic/src/proof/tests/gate.rs`, `crates/tatic/src/jit/lower_wat.rs` (`read` emits the `local.get` row), `docs/TOUR.md`
- Delete: `crates/tatic-wasm/src/machine/laws.rs`

**Interfaces:**
- Consumes: `w2:wasm.rs` (`fr`, `frame`, `nth`, `getter`, `words`, `split_args`; not `put`, `setter`, `LocalSet`, `ConstI`, `GetI`, `K::I`, `Hooks::{lab, ret}`); `w2:wasm/sim.rs` (`SEnv`, `SrcFn`, `G`, `cong`, `spine`, `Sim::{sim, cont_rel, sim_step}` minus the call rule; `binders` minus the temporaries).
- Produces, in `machine.rs`:
  - `Machine<'t> { pub n: usize, pub fw: usize, pub table: &'t Table }`; `pub fn fr(&self) -> Expr` (`V^fw x V`); `pub fn frame(&self, vals: &[Expr]) -> Expr` (`vals` at slots `0..`, zeros up to `fw`, a terminal zero word); `G A = Fr -> A -> Mem -> R`; `Ret = V -> Mem -> R`; `Mem` keeps today's type and nothing reads it.
  - The `Const` class's operand is `Fr -> V`: row `const`'s meaning is `\_:Fr. lit n v`; a new row `local.get` (`Const`, meaning the frame projection at the operand, failing at or past `fw`, printed `local.get $p{i}`). `Ins::LocalGet` is deleted; the lowering's `Read::Param(li)` emits `Ins::Row { name: "local.get", operand: li }`.
  - `pub struct MeaningEnv { pub r: At, pub ch: Option<At> }` (T10 adds the callee environment); `pub fn meaning(&self, c: &mut Cx, p: At, k: At, me: &MeaningEnv) -> Expr`, with no fuel and no `z`; an `If` uses `ch` when `Some`, else `choose`.
  - Deleted: `Ins::Store`, `Ins::Load`, their constructors, `upd`, the `Loop` constructor and interpreter, the interpreter's fuel argument (today's `nat2_lit(0)` passed to `meaning`, as in `w2:wasm/sim.rs#bm`'s `fuel0`, goes with it), `Machine::{good, append, ifp, spec}` (their only users are in `laws.rs`), `laws.rs` whole (`if_inv`/`Ctl`, `append_law`, `if_law`, `if_good`, `loop_law`, `timeout`, `run_by_refl`, `run_wasm_checks`, `wasm_programs_as_kernel_data`, `wasm_scaling`). `nat2_lit` itself stays in `machine.rs`: it is the Church-numeral builder, and T11's `quantify_fuel: false` mutant builds its fixed fuel numeral with it.
- Produces, in `machine/statement.rs` (trusted):
  - `pub type SrcFn<'a> = dyn Fn(&mut Cx, &SEnv, &dyn Fn(&mut Cx, Expr) -> Expr) -> Expr + 'a;`
  - `pub struct SEnv { pub n: usize, pub r: At, pub g: At, pub params: Vec<At>, pub ch: Option<At>, pub fuel: At, pub own: usize, pub callees: Vec<(usize, At)> }` with `pub fn choose(&self, c: &Cx, cond: Expr, t: Expr, e: Expr) -> Expr` and `pub fn call(&self, c: &mut Cx, pos: usize, args: &[At], k: &dyn Fn(&mut Cx, Expr) -> Expr) -> Expr` (position `own` applies `g`, another a callee's source function; one method, where w2 had `call` and `call_fn`).
  - `pub struct ModEntry<'a> { pub entry: &'a Entry, pub src: &'a SrcFn<'a> }`; a module is `&[Option<ModEntry>]` indexed by position.
  - `pub fn statement(m: &Machine, module: &[Option<ModEntry>], entry: usize) -> Expr`: `Pi N (GoodNat N) R z, law_entry`, every law, the motive, the step and the hypothesis on the one telescope `d, a.., mu, km, ks, rel` (w2's `G::binders` without temporaries). T11 splits it for O3's seam; here it is the plain builder.
- Produces, in `machine/sim.rs` (untrusted): `pub fn prove(m: &Machine, module: &[Option<ModEntry>], entry: usize) -> Result<Expr, String>` (the proof of `statement`'s proposition: `GoodNat` induction, then the walk with the return and `choose`/congruence rules; no call rule yet, so a body with `Call` is `Err`).
- Produces, in tatic `proof/gate.rs`: `Source::cps` reshaped per D4's seam: `fn source_fn<'s>(table: &'s Table, store: &'s TermStore, h: Hash) -> Option<(usize, Box<SrcFn<'s>>)>` strips an optional `Rec`, then `arity` `Abs`, reads the body through `shape::classify`, accepts (in this task) `If` on a comparison in tail position, parameter `Var`, `Lit`, a `Prim` whose row is `Word`, and returns the arity and a total closure (it takes `ch` through `SEnv`). The refl `statement` and its fuel parameter go. `pub(crate) fn build(table: &Table, store: &TermStore, h: Hash, arity: usize, code: &[Ins]) -> Option<(Expr, Result<Expr, String>)>` returns the statement and the generator's proof apart (`None` when `in_fragment` or `well_formed` fails), over a one-entry module at `fw = arity`; the work guards, `measure_gate_costs`, `measure_cachegrind` and `time_doubling_12` call it where they called the refl `statement`, so build and check stay timed apart. `gate(table, store, h, arity, code) -> bool` is `build` then `holds(proof, stmt)`. T10 generalises `build` to a fragment and turns the `Option` into a `Result` whose `Err` is the verdict.

- [ ] **Step 0 (on the plan branch, before switching): the refl reference.** Add `#[test] #[ignore] fn time_doubling_12()` to `proof/tests/gate.rs`: build `doubling(12)`'s refl `statement(..)` (the proof and statement apart), then check it with `holds`, on a `CHECK_STACK` thread; print one line `build_ms <x> check_ms <y>` (Step 4 points it at `build`). Commit it (test-only). Build the test exe (`BUILD(<folder>-build, "cargo test -j 10 -p tatic --lib --no-run")`) and copy it into folder `v08-refl-exe` (the `cp` line in Global Constraints).
  ```bash
  git add crates/tatic/src/proof/tests/gate.rs
  git commit -m "test: time_doubling_12, the go/no-go's reference measurement"
  ```
- [ ] **Step 1: Write the failing tests (step 1's).**
  ```rust
  // machine.rs tests
  #[test] fn local_get_reads_the_frame()   // rewritten: code [local.get 1, local.get 0, sub] over frame [a, b] at fw 2
  //   answers sub b a by refl and not sub a b; local.get 2 at fw 2 panics ("out of the frame's width")
  #[test] fn frame_pads_with_zeros()       // frame([x]) at fw 3 is (x, (0, (0, 0))) by def_eq
  // wasm.rs tests: T3's test, updated for the new Const operand and row set
  #[test] fn wasm_rows_are_closed_and_typed()
  //   table()'s rows are exactly const, local.get, add, sub, mul, lt, le, eq, lt_u; at n = 8, fw = 2: a Const row's
  //   meaning infers Fr -> V (const at operand 3, local.get at operands 0 and 1), Word V -> V -> V, Bit V -> V -> Bv_1
  ```
  Run: `cargo test -p tatic-wasm local_get_reads_the_frame`. Expected: compile error (`Machine::frame` not found). Step 2's run also covers the updated `wasm_rows_are_closed_and_typed`.
- [ ] **Step 2: Implement step 1** (frame, memory argument, `local.get` row, the deletions). Run: `cargo test -p tatic-wasm --lib machine && cargo test -p tatic-wasm --lib wasm_rows_are_closed_and_typed`. Expected: the three tests PASS (the crate's other tests may be red until Step 4).
  ```bash
  git add -A crates/tatic-wasm crates/tatic/src
  git commit -m "tatic-wasm: locals as a frame passed in beside one opaque memory; local.get is a row; Store, Load, upd, the loop constructor, fuel and laws.rs deleted (D2; branch, red until the statement lands)"
  ```
- [ ] **Step 3: Write the failing tests (step 2's).**
  ```rust
  // machine/sim/tests.rs (a mini source language as w2:wasm/sim/tests.rs's `Src`, ported without temporaries or calls; T10 adds its self-call)
  #[test] fn prove_accepts_straight_line_and_if()        // \a b. a - b; \a b. if a < b then a * 2 else b + 1;
                                                         // each holds(prove, statement) at n = 8 and n = 64
  #[test] fn prove_refuses_a_swapped_if_and_a_wrong_row()// the If arms swapped; sub for add: prove is Err naming the path
  // proof/tests/gate.rs: gate_accepts_the_fragment_table and gate_rejects_mutations keep their term lists
  //   (the_five(): inc, doubling_4, straight_line, a_capturing_closure_call, a_pap_capturing; the fragment table adds
  //   a - b, third, doubling_12, a + MIN); the LocalGet mutators become local.get-row mutators and keep the arity < 2
  //   skip (there is no shape check until T10; T11 drops the skip and re-derives the lists)
  ```
  Run: `cargo test -p tatic-wasm prove_accepts`. Expected: compile error (`sim::prove` not found).
- [ ] **Step 4: Implement step 2** (statement, straight-line walk, `source_fn`, `gate` rewired). Run: `SUITE(t9-suite)`. Expected: exit 0, goldens unchanged; `gate_check_work_is_linear_in_the_tree` and `gate_build_work_is_linear_in_the_tree` pass under 2.05 (they call `build`); `time_doubling_12` now calls `build` and prints the same line.
- [ ] **Step 5: The go/no-go.** Same session: `TRUN(bench, s2c-refl-doubling12, "EXE(v08-refl-exe, proof::tests::gate::time_doubling_12 --ignored --exact --nocapture)")`, 5 times, then build this commit's exe untimed (`BUILD(<folder>-build, "cargo test -j 10 -p tatic --lib --no-run")`), copy it into folder `v08-rel-exe`, and run it 5 times the same way as `s2c-rel-doubling12`. Each run's `out.log` must hold the `build_ms .. check_ms ..` line; a run without it (0 tests ran) is rerun, never counted. Expected: the relational median at most 0.57 s and at most 1.5 times the refl median. **No-go:** stop and report (the user amends Goal 5's cap floor); main and the plan branch keep T1-T8; the sub-branch stays as the record.
- [ ] **Step 6: Guard loop** (TOUR: `machine/statement.rs`, `machine/sim.rs`, the `local.get` row, the frame; `laws.rs`, `upd`, `Store`/`Load` removed; amend `MAX_GATE_TREE`'s doc if the median is above 0.4 s), **commit and merge on go.**
  ```bash
  git add -A crates/tatic-wasm crates/tatic/src docs/TOUR.md docs/runs.md
  git commit -m "machine: the one statement (module fixpoint over fuel, one law telescope) and the generator's straight-line walk replace the refl path (D4); go/no-go median <x> s"
  git switch v08-recursion-once && git merge --no-ff v08-s2c-frame -m "merge S2c steps 1-2 (go/no-go: go)"
  ```

### Task 10: S2c step 3, part 1: `Call`'s meaning, the call rule, self-calls in `cps`, the verdict, the shape check

**Files:**
- Modify: `crates/tatic-wasm/src/machine.rs`, `crates/tatic-wasm/src/machine/statement.rs`, `crates/tatic-wasm/src/machine/sim.rs`, `crates/tatic-wasm/src/machine/sim/tests.rs` (the mini `Src` gains a self-call), `crates/tatic/src/proof/gate.rs`, `crates/tatic/src/jit.rs`, `crates/tatic/src/proof/tests/gate.rs`, `crates/tatic/src/jit/tests.rs`, `crates/tatic/src/proof/tests/baseline.rs`, `docs/TOUR.md`

**Interfaces:**
- Consumes: T6's `Entry`, `EnvAccess`, `CompiledFragment::{records, entry_pos}`; T9's `Machine`, `MeaningEnv`, `statement`, `prove`, `source_fn`.
- Produces, in `machine.rs`:
  - The `Call` structural class: constructor `[unpack, idx, rest]` with no type operands (O1, tried first in Step 1); `unpack : S -> Fr x A` builds the callee's padded frame (parameters at `0..arity`, zeros after) and binds no answer type (`w2:wasm.rs#unpack` without the `K::I` slots); `idx` is `lit(n, j)`. Its meaning continues into environment entry `j` and then the meaning of `rest`; for an empty `rest` that is the fold's own continuation (T5's form).
  - `MeaningEnv { r, ch, calls: Option<(At, Vec<usize>)> }`: the callee environment (`V -> Fr -> Mem -> Ret -> R`) and each position's arity.
  - `pub fn shape_check(table: &Table, records: &[Option<&Entry>]) -> Result<(), String>`, the shape check: each record's body runs from `[]` to `[W]` (T6's `well_formed(table, &e.code, &[], &arities)`, with `arities` the records' arities by position), holds no `Raw` and no unknown row, each `local.get` operand is below that record's `arity`, each `Call(j)` names a record, and every record's env is `Params(0)`. T6's `well_formed` keeps its name and signature.
- Produces, in `machine/statement.rs`: the module fixpoint over fuel, `N H z B_j` per position (w2's `Ctxt::{table, real, law}` over `ModEntry` positions), callee laws as hypotheses discharged by the callee's closed proof (`w2:wasm/sim.rs#closed`), at the module's `fw` (the widest record's arity).
- Produces, in `machine/sim.rs`: the call rule (`w2:wasm/sim.rs#sim_step`'s third branch, one rule for the function's own position through the induction's `j` and for every other through the outer `N`; it checks the source's head, body and arity, reads the frame's pair spine, checks each parameter slot against the source argument and the padding against 0, then applies the law). Three walk rules in all.
- Produces, in tatic `proof/gate.rs`:
  - `pub enum Layer { Shape, Walk, Kernel }` and `pub enum Verdict { Accepted, Rejected(Layer, String), NotCovered(String) }`.
  - `pub const CALL_WEIGHT: u64 = 0;` beside `MAX_GATE_TREE` (which becomes `pub(crate)`, so the budget tests name it); `pub(crate) fn call_sites(store: &TermStore, h: Hash) -> u64`: the `Shape::SelfCall` and `Shape::CombinatorCall` nodes `shape::classify` reads in `h`'s body (after the optional `Rec` and the `Abs` binders, the same reading `source_fn` does); `fn cost(store: &TermStore, h: Hash, callees: &[Hash]) -> u64` = `tree_size(store, h)` plus `CALL_WEIGHT` times `call_sites` summed over `h` and `callees`. It reads the source and the registry-derived module only, never the `Ins` list (Global Constraints, Budget). T10 passes `&[]`; T14 passes the registry's callee terms.
  - `pub(crate) fn build(table: &Table, store: &TermStore, h: Hash, frag: &CompiledFragment) -> Result<(Expr, Result<Expr, String>), Verdict>` (T9's `build` generalised in place: its `Option` becomes this `Result`; the work guards, `measure_gate_costs`, `measure_cachegrind` and `time_doubling_12` destructure the `Ok` pair as they did the `Some`): `Err(NotCovered(..))` when `source_fn` is `None`, `cost` is over `MAX_GATE_TREE`, or the module holds a record other than the entry (until S3; read from the registry-derived module, not the code); `Err(Rejected(Shape, ..))` when `shape_check` fails; else `Ok((statement, the generator's result))`.
  - `pub fn gate(table: &Table, store: &TermStore, h: Hash, frag: &CompiledFragment) -> Verdict`: `build`'s `Err` as it is; on `Ok`, a proof `Err` is `Rejected(Walk, ..)`, a kernel refusal `Rejected(Kernel, ..)`, else `Accepted`; under `scoped` on the caller's thread.
  - `source_fn` gains `Shape::SelfCall`: its arguments evaluated left to right, then `SEnv::call(own, ..)`.
  - Deleted: `in_fragment`, `tail`, `operand`, the old `gate` and `statement`, the `arity == 0` clause and the `unreachable!` arms.
- Produces, in `jit.rs`: `fn prove_install(terms: &TermStore, h: Hash, frag: &CompiledFragment) -> bool` = `match gate(wasm_table(), ..) { Accepted => true, Rejected(..) => false, NotCovered(_) => kernel_verify(terms, h, frag.arity) }`.

- [ ] **Step 1: O1.** Write `#[test] fn call_constructor_types_without_sort_operands()` in `machine.rs`: `prog` over `[const 1, Call(0)]`, `[const 1, const 2, Call(1)]` and a 3-argument call, each `infer`s. Run: `cargo test -p tatic-wasm call_constructor_types`. Expected: compile error, then after implementing the constructor, PASS. **Fallback** (D3): if it does not type, keep w2's explicit binders `[A, S, unpack, idx, rest]`, rename the test `call_constructor_types_with_sort_binders`, and add the `PARKED.md` line the spec names.
- [ ] **Step 1b: Give the mini source language a self-call.** In `machine/sim/tests.rs`, `Src` gains `SelfCall(Vec<Src>)` (arguments left to right, then `SEnv::call(own, ..)`, as `w2:wasm/sim/tests.rs`'s `Src` has it). Write `#[test] fn prove_accepts_a_sum_loop_and_factorial()` (the sum loop `rec f n acc = if n <= 0 then acc else f (n - 1) (acc + n)` and factorial in `Src`, each with its hand-written code: `holds(prove, statement)` at n = 8 and 64) and `#[test] fn prove_refuses_a_swapped_call_argument()` (the sum loop's code with the two arguments' instructions exchanged: `prove` is `Err`). Run: `cargo test -p tatic-wasm prove_accepts_a_sum_loop`. Expected: FAIL (`prove` is `Err` on a body with `Call`) until Step 3. T11's statement mutants use this sum loop.
- [ ] **Step 2: Write the failing tests.**
  ```rust
  // proof/tests/gate.rs
  #[test] fn gate_accepts_the_goal_1_targets()
  //   capturing_closure_loop, partial_application_loop, factorial, redundant_arithmetic_recursion, fib, each
  //   specialised (compile_specialised; the term and code try_install proves): gate(..) == Accepted
  #[test] fn gate_accepts_the_fragment_table()            // the five v0.7 terms and doubling(12): Accepted
  #[test] fn gate_accepts_a_permuting_tail_call()         // Review Focus 1: Accepted; jit.apply == eval at (3, 7), (0, 5)
  #[test] fn gate_accepts_extreme_literals_in_call_arguments()
  //   Review Focus 2: rec f n acc = if n <= 0 then acc else f (n + MIN) (acc + -1), built with s.lit(i64::MIN),
  //   s.lit(-1): Accepted; jit.apply == eval at (1, 0), (-5, 9)
  #[test] fn gate_accepts_a_call_in_a_condition()         // Review Focus 3: Accepted
  #[test] fn gate_accepts_mixed_tail_and_non_tail_calls() // Review Focus 4: Accepted
  #[test] fn a_record_with_an_env_parameter_is_rejected_by_the_shape_check()
  //   factorial's fragment with the entry's env set to Params(1): Rejected(Shape, _)
  #[test] fn covered_code_with_raw_or_ill_formed_is_rejected_and_not_installed()
  //   factorial's body with Raw("nop") appended; with its last instruction dropped: Rejected(Shape, _), and
  //   prove_install(..) is false
  #[test] fn what_cps_cannot_take_is_not_covered()
  //   twice; \f. f 1; \a b. 1 + (if a < b then a else b); \a b. if (if a < b then a else b) < 1 then 1 else 0;
  //   \a b. a / b; gcd (Mod); \a. a / 0: NotCovered; each installs as its BASELINE row says
  #[test] fn a_term_over_the_budget_is_not_covered()
  //   doubling(13) (tree_size over MAX_GATE_TREE): gate(..) == NotCovered; jit.apply == eval at 3; it installs as its
  //   BASELINE row says, through kernel_verify. Second case, under `if CALL_WEIGHT > 0` in T10 (T12 turns the guard into an assert): a self-call
  //   term (time_call_family's shape) with k = call_sites sites built so that tree_size <= MAX_GATE_TREE <
  //   tree_size + CALL_WEIGHT * k: NotCovered, so the weight term of cost is exercised
  #[test] fn a_closed_straight_line_term_takes_the_gate()  // 3 + 4 at arity 0: Accepted
  #[test] fn a_module_with_a_callee_is_not_covered_until_s3() // twice_inc_5 specialised: NotCovered
  #[test] fn extra_calls_in_covered_code_are_rejected_not_uncovered()
  //   factorial's entry code with 64 extra Call(entry) instructions appended (and with them inserted before its last
  //   instruction): Rejected(_, _), never NotCovered; prove_install false. cost takes no code, so the padding cannot
  //   move it at any weight; T12's run (Step 3) repeats the test under the fitted weight
  // jit/tests.rs
  #[test] fn the_gates_verdict_is_final_for_covered_terms()
  //   straight_line and factorial, specialised: prove_install true; with the If arms swapped, false, although
  //   kernel_verify alone is true for the same term
  ```
  Delete `in_fragment_rejects_the_rest` (its cases are `what_cps_cannot_take_is_not_covered`'s, and its `doubling_13` case is `a_term_over_the_budget_is_not_covered`'s) and `calls_go_to_kernel_verify_until_the_gate_covers_them`. In `jit/tests.rs`, migrate the callers of the old `prove_install` and `in_fragment`: delete `the_gates_verdict_is_final_for_fragment_terms` (its straight_line case and If-arm swap are `the_gates_verdict_is_final_for_covered_terms`'s); `the_installation_proof_is_about_the_specialised_term` calls `prove_install(&sp.store, sp.term, &c.frag)`; `an_operand_if_installs_through_the_chain` asserts `matches!(gate(shape::wasm_table(), &s, h, &frag), Verdict::NotCovered(_))`, with `frag` from `compile_specialised`, in place of `!in_fragment(..)`. The existing callers of `gate` in `proof/tests/gate.rs` (`gate_accepts_the_fragment_table`, `gate_rejects_mutations`, the work guards) move to the fragment signature and assert on the `Verdict` (`Accepted`, or `!= Accepted` for a mutant); their lists stay as T9 left them until T11.
  Run: `cargo test -p tatic --lib gate_accepts_the_goal_1_targets`. Expected: compile error (`Verdict` not found).
- [ ] **Step 3: Implement** the Interfaces (start from `w2:wasm/sim.rs`'s hunks named above; keep `machine.rs`, `statement.rs` and `sim.rs` each under 1000 lines, `wc -l`).
- [ ] **Step 4: Run.** `SUITE(s2c-step3-suite)`. Expected: exit 0; goldens unchanged since T6; `gate_accepts_the_goal_1_targets` passes in under 10 s per target at n = 64 (a slower target is a T12 stop).
- [ ] **Step 4b: Goal 5's cap floor with `Call` in the machine.** T9's go/no-go ran before `Call`'s constructor existed (this plan tries O1 here, not in S2c step 1), and every Church-encoded program now carries one more constructor binder. Build this commit's test exe untimed (`BUILD(<folder>-build, "cargo test -j 10 -p tatic --lib --no-run")`), copy it into folder `v08-call-exe`, and rerun T9 Step 5's relational protocol: `TRUN(bench, s2c-call-doubling12, "EXE(v08-call-exe, proof::tests::gate::time_doubling_12 --ignored --exact --nocapture)")` 5 times, each `out.log` holding the `build_ms .. check_ms ..` line. Expected: median at most 0.57 s. **Stop** for the user on a miss (the cap floor is the user's call, Goal 5); the median goes in T13's findings beside T9's.
- [ ] **Step 5: Guard loop** (TOUR: `Call`'s class, `Verdict`, `Layer`, `shape_check` over records, `in_fragment` and the refl `statement` removed from the data flow), **commit.**
  ```bash
  git add crates/tatic-wasm crates/tatic/src docs/TOUR.md docs/runs.md PARKED.md
  git commit -m "gate: Call over a module position, the one call rule, self-calls in cps, the three-way verdict and the shape check over records (D3, D4); doubling(12) median <x> s with Call"
  ```

### Task 11: S2c step 3, part 2: Goal 4's S2c mutant set, the statement mutants (O3), held-out tests ignored

**Files:**
- Create: `crates/tatic/src/proof/tests/held_out.rs`, `crates/tatic/src/proof/tests/gate_mutants.rs`
- Modify: `crates/tatic/src/proof/tests.rs` (`mod held_out;` in the first commit, `mod gate_mutants;` in the second), `crates/tatic/src/proof/tests/gate.rs` (`gate_rejects_mutations` moves out), `crates/tatic-wasm/src/machine/statement.rs` (the seam and its `cfg(test)` tests), `crates/tatic/src/testing/ins_mutate.rs`

**Interfaces:**
- Consumes: T10's `build`, `gate`, `Verdict`, `Layer`; T10's mini `Src` sum loop; `testing::ins_mutate::mutate`.
- Produces:
  - In `gate_mutants.rs`: `fn forged_rejected(table: &Table, pos: (&TermStore, Hash, &CompiledFragment), mutant: (&TermStore, Hash, &CompiledFragment))`: `build` the positive case's proof and the mutant's statement; assert `holds(proof, stmt)` is `Err` (w4's method). It runs only on a mutant for which `build` returns `Ok((stmt, _))` and whose statement differs from the positive case's (code and source mutants); it panics on an `Err` from `build`. A mutant `build` refuses (`Err(Rejected(Shape, ..))`: no statement exists to forge against) is asserted with `rejected_by(.., Layer::Shape, ..)` alone. "Forged" in the tests below (and T15's) always means "forged where `build` gives the mutant a statement".
  - `fn rejected_by(v: Verdict, layer: Layer, what: &str)`: asserts `Rejected(layer, _)`, printing the reason.
  - In `statement.rs`, this task's one-time split of T9's plain builder (O3's seam has one owner): `struct Clauses { relate: fn(&mut Cx, At, At, At, At) -> Expr, quantify_fuel: bool }` (`relate` builds the continuation relation hypothesis from `r, km, ks, v`); `const FIXED: Clauses`; the private `fn statement_with(m: &Machine, module: &[Option<ModEntry>], entry: usize, cl: &Clauses) -> Expr` takes T9's body, and the public `statement` becomes `statement_with(m, module, entry, &FIXED)`, the only value it passes. Its `cfg(test)` tests (in `machine/statement/tests.rs` if past 299 lines, a child module so it reaches the private items) pass `RELATE_IGNORES_K` (`km a mu = ks 0`) and `quantify_fuel: false` (the statement at one fixed fuel numeral).
  - **O3 stop:** if the seam needs anything beyond a private `Clauses` and the one public entry passing `FIXED`, the statement mutants go to `PARKED.md`, Goal 4's text gets a line saying so, and `statement` stays T9's plain builder.

- [ ] **Step 1: The held-out test, alone** (the spec's test-only commit). Create `held_out.rs` with `#[test] #[ignore] fn held_out_terms_are_accepted()`: `held_out_a`, `held_out_b` specialised: `gate(..) == Accepted`, and `JitEngine::apply` installs each (`stats.compiled == 1`), Goal 5's "must now install" for the held-out rows. Add `mod held_out;` to `proof/tests.rs`. Run: `cargo test -p tatic --lib held_out`. Expected: 0 passed, 1 ignored.
  ```bash
  git add crates/tatic/src/proof/tests/held_out.rs crates/tatic/src/proof/tests.rs
  git commit -m "test: held-out terms asserted Accepted, ignored until the freeze"
  ```
- [ ] **Step 2: Write the mutant tests.** Each names its layer as observed; where the spec does not fix it, the first run decides and the test pins it. `gate_rejects_mutations` moves from `proof/tests/gate.rs` to `gate_mutants.rs`. Its terms are six: `the_five()` (`inc`, `doubling_4`, `straight_line`, `a_capturing_closure_call`, `a_pap_capturing`) plus factorial (spec S2c "Done when"). Its mutation lists are re-derived (spec "Plan inputs": under D2 a slot past the function's own width is `Rejected` by the shape check): the `arity < 2` skip for the `local.get` mutators goes, and each mutation's `applies` list is the set of the six terms whose code it changes, read from the test's own `changed` assertion on a first run with every `applies` list set to all six (the failures name the terms it does not change), then written in. Each case is asserted with `rejected_by(..)` and, where its statement differs, `forged_rejected(..)`: one list, one test.
  ```rust
  // gate_mutants.rs
  #[test] fn gate_rejects_mutations()               // moved, as above
  #[test] fn every_row_has_an_operator_swap_mutant()// for each Word/Bit row r of wasm_table(), on its carrier: r replaced
  //   by another row of its class is Rejected, forged too. Carriers: add, sub, mul, lt, le on the census term that
  //   holds r (the first in census order with a covered verdict); lt_u (no source operator) as the code-level swap
  //   lt to lt_u on straight_line, as v0.7 does; eq (no covered census term holds it) on a term local to this test,
  //   \a b. if a == b then a else b, swapped eq to lt. The test asserts every Word/Bit row has a carrier.
  #[test] fn an_if_arm_swap_is_rejected()           // straight_line and factorial
  #[test] fn self_call_site_mutants_are_rejected()
  //   for each self-call site of factorial, fib and capturing_closure_loop: a local.get argument index changed,
  //   two arguments swapped, an argument instruction dropped, one added, the Call dropped (its arguments popped
  //   by nothing: the shape check); each Rejected with its layer; forged only where build gives a statement (the
  //   dropped and added argument instructions and the dropped Call are Rejected(Shape) with no forgery)
  #[test] fn no_loop_spike_controls_are_rejected()  // the no-loop spike's control list (doc 15's section "Tail
  //   self-calls as `return_call`, with no `loop` or `br`: a spike"), minus its return_call-for-call mutant
  #[test] fn real_term_controls_are_rejected()      // factorial mul to add, fib add to sub: Rejected; forged
  #[test] fn factorials_proof_does_not_prove_fibs_statement() // the kernel negative for a self-call term
  // statement.rs tests (tatic-wasm, T10's sum loop in the mini source language)
  #[test] fn a_relation_that_ignores_the_continuation_breaks_the_proof() // holds(prove(..), statement_with(.., RELATE_IGNORES_K)) is Err
  #[test] fn an_unquantified_fuel_breaks_the_proof()                     // quantify_fuel: false: Err
  ```
  Run: `cargo test -p tatic --lib gate_mutants && cargo test -p tatic-wasm statement`. Expected: the seam tests fail to compile (`statement_with` not found) until Step 3; each mutant test PASSES once its layer is pinned (a mutant that is `Accepted` is a soundness finding: stop and report).
- [ ] **Step 3: Implement the seam** as in Interfaces. Run the two commands again, then `cargo test -p tatic --lib gate`. Expected: PASS.
- [ ] **Step 4: Guard loop, commit.**
  ```bash
  git add crates/tatic-wasm/src/machine crates/tatic/src/proof/tests crates/tatic/src/proof/tests.rs crates/tatic/src/testing PARKED.md
  git commit -m "gate: S2c's Goal 4 set (rows, If arms, self-call sites, spike controls, forged proofs; gate_rejects_mutations moved beside them) and the statement mutants through a private clause record (O3)"
  ```

### Task 12: S2c the `Call` weight fit

**Files:**
- Create: `docs/runs/<date>/scripts/v08-weight-fit.sh` (header comment in its first four lines), `crates/tatic/src/proof/tests/gate.rs` gains `#[test] #[ignore] fn time_call_family()`
- Modify: `crates/tatic/src/proof/gate.rs` (`CALL_WEIGHT`)

**Interfaces:**
- Produces: `CALL_WEIGHT: u64` fitted; `time_call_family` builds `rec f n = if n <= 0 then 0 else f (n-1) + .. + f (n-1)` with `k` call sites (`k` = `call_sites(store, h)`, the source count `cost` reads; the test asserts it equals the number of `f` applications built), `k` in 1, 2, 4, ... up to 64, and prints `k tree_size build_ms check_ms`.

- [ ] **Step 1: Run** Build the test exe untimed (`BUILD(<folder>-build, "cargo test -j 10 -p tatic --lib --no-run")`) and copy it into folder `v08-fit-exe`; then `TRUN(bench, s2c-weight-fit, "bash docs/runs/<date>/scripts/v08-weight-fit.sh")` (the script runs that copy through `v08-exe.sh v08-fit-exe ...` as `proof::tests::gate::time_call_family --ignored --exact --nocapture` 5 times, takes the medians per `k`, writes them to `headline.txt`, and exits non-zero if a run printed no timing line).
- [ ] **Step 2: Fit.** `CALL_WEIGHT` is the per-site cost in nodes at which `tree_size + w * k` reaches `MAX_GATE_TREE` exactly when the measured time reaches T9's relational median. Then check every Goal 1 target's `cost` is under `MAX_GATE_TREE`; **if not, lower the weight** and record why. **Stop** if any Goal 1 target alone checks slower than T9's median (from T10's suite times; time it here to be sure).
- [ ] **Step 3: Run** `cargo test -j 10 -p tatic --lib gate`. Expected: PASS, `extra_calls_in_covered_code_are_rejected_not_uncovered` and `a_term_over_the_budget_is_not_covered` among them under the fitted weight; the latter's second case now runs (it asserts `CALL_WEIGHT > 0`: a fit of 0 is a finding for T13 and drops that case with a comment saying so).
- [ ] **Step 4: Commit.**
  ```bash
  git add crates/tatic/src/proof/gate.rs crates/tatic/src/proof/tests/gate.rs docs/runs docs/runs.md
  git commit -m "gate: the Call weight fitted to the relational doubling(12) median (<w> nodes per site)"
  ```

### Task 13: S2c step 4: the freeze, the verdict column, the timed targets, the docs and findings

**Files:**
- Create: doc 15's section files 26 ("v0.8's build: measurements and checks") in its folder, with its line in `docs/tier-cycle/README.md`
- Modify: `crates/tatic/src/proof/tests/baseline.rs` (`VERDICTS`), `crates/tatic/src/proof/tests/held_out.rs` (Step 8, its own commit), `ROADMAP.md`, `PARKED.md`, `docs/decisions/2026-11-10-v08-shape-and-any-backend.md`, `docs/tier-cycle/README.md`, `docs/TOUR.md`, `docs/proven.md`, and any deletion steps 1-3 left (`rg` below)

**Interfaces:**
- Produces: `pub(super) const VERDICTS: &[(&'static str, Verdict kind)]` for every census and held-out row (`Accepted`, `Rejected`, `NotCovered`), and `#[test] fn verdicts_match()`: the measured verdict of each row equals the table. The measured verdict is `gate(..)` on the form `try_install` proves: the specialised term and fragment when `compile_specialised` gives one, else the term and its own `compile` fragment; a term with no fragment at all never reaches `prove_install` and is `NotCovered` by this rule. The rules the table must satisfy, asserted by the test beside the literal: every row whose `records()` hold a `Raw` or heap line is `NotCovered` (Goal 5); the Goal 1 targets are `Accepted`; no census row is `Rejected` (each runs correct code, so a `Rejected` row is a walk gap that loses an install, spec D4 "Cost": stop and report). The held-out rows are written as measured; one that is not `Accepted` is Goal 3 failed and goes to Step 8's fork, never to a generator fix before the freeze. The literal is filled from a print helper, not by hand (the install outcomes stay `baseline_fixture_matches`'s, with its one `HELD_OUT` exception; the held-out rows' must-install is `held_out_terms_are_accepted`'s, Step 8).

- [ ] **Step 1: Finish the deletions.** Run `rg -n 'in_fragment|strip_loop|gate_with|upd\b|Ins::Store|Ins::Load|LocalGet|loop_law|run_by_refl|wasm_scaling|SelfCall \{ args, tail' crates`. Expected: empty; delete what remains.
- [ ] **Step 2: Write `verdicts_match`**, fill `VERDICTS` from a print helper, run `cargo test -p tatic --lib baseline`. Expected: PASS.
- [ ] **Step 3: Time the targets** in one recorded run: `TRUN(bench, s2c-targets, "EXE(v08-targets-exe, proof::tests::gate::time_targets --ignored --exact --nocapture)")` (exe built untimed with `--no-run` and copied into folder `v08-targets-exe` first), where `#[test] #[ignore] fn time_targets()` (in `proof/tests/gate.rs`) prints `name cost build_ms check_ms` for the Goal 1 targets, the five, `doubling(12)` and the held-out terms. Expected: every Goal 1 target under the budget.
- [ ] **Step 4: Docs grep.** `rg -n "in_fragment|refl path|fuel 1|loop \$L|\(loop|countdown|Store|Load|wasm/laws|LocalGet|op_of|header string|EnvAccess::None" ROADMAP.md PARKED.md docs/TOUR.md docs/proven.md docs/decisions docs/tier-cycle/README.md`, and fix every hit outside dated history: ROADMAP's v0.8 line (S2 done; S3, S4 left), `PARKED.md`, the decision file's "Open for the spec" section and its stale-D2 notes, the README's v0.8 claims, TOUR's prose, `docs/proven.md` (the three-way verdict for the `in_fragment` paragraph; the trusted list gains the tail rule, the header from the record, the frame and memory, and loses `loop` and the `$p0..` header claim). The closing report lists each file fixed or found current.
- [ ] **Step 5: Findings.** Section 26 holds, with run ids: S0's icount A/B (T4), S2a's verdicts (T5), S2b's benches (T5, T7), the go/no-go (T9) and its rerun with `Call` (T10 Step 4b), the weight fit (T12), the targets' times (Step 3); and "Guard: none added, the deleted items are code symbols, so the compiler fails on any use, and the docs grep covers prose".
- [ ] **Step 6: Workspace run.** `RUN(gate, s2c-workspace, "cargo test -j 10 --workspace")`. Expected: exit 0; `git diff --stat <T6's commit> -- crates/tatic/tests/golden` empty.
- [ ] **Step 7: Guard loop, commit** (this commit is the freeze: every non-test file under `crates/` is frozen until T14 starts).
  ```bash
  git add crates docs ROADMAP.md PARKED.md
  git commit -m "v0.8 S2c closed: verdict column, targets timed, docs updated, findings (freeze)"
  ```
- [ ] **Step 8: Goal 3, the held-out check** (after the freeze commit, its own commit). Un-ignore `held_out_terms_are_accepted` (touch only `crates/tatic/src/proof/tests/held_out.rs`). Run: `cargo test -j 10 -p tatic --lib held_out`. Expected: PASS. Check `git diff --stat HEAD -- crates` lists only that test file. **On failure, stop** (the fork rule): S3 and S4 wait for the user, who chooses between amending the generator with a new held-out pair (the freeze reopens once) and dropping the no-per-function-case claim as a recorded finding. On PASS, commit:
  ```bash
  git add crates/tatic/src/proof/tests/held_out.rs
  git commit -m "test: held-out terms accepted against the frozen generator (Goal 3)"
  ```

### Task 14: S3 modules: entries' sources, the registry pairing, closed heads in `cps`, Goal 2

**Files:**
- Create: `crates/tatic/src/proof/tests/modules.rs` (`mod modules;`)
- Modify: `crates/tatic/src/jit/compile.rs` (sources from the registry), `crates/tatic/src/jit/lower_wat.rs` (`Item::Func` construction), `crates/tatic/src/proof/gate.rs`, `crates/tatic-wasm/src/machine/statement.rs` and `sim.rs` only if a several-entry module needs it, `crates/tatic/src/proof/tests/baseline.rs` (`VERDICTS` re-filled, Step 2b), `crates/tatic/src/proof/tests/gate.rs` (one test deleted, Step 2b), doc 15 (a new section 27 "v0.8's modules: measurements"), `docs/tier-cycle/README.md`, `docs/TOUR.md`

**Interfaces:**
- Consumes: T10's `build`, `statement`, `prove`, `source_fn`, `Verdict`.
- Produces:
  - In `compile.rs`: `Item::Func { pos: usize, entry: Entry, source: Option<Hash> }` (the registered term from `PendingCombinator::Literal`, `None` for a wrapper position, `Some(h)` for the entry), read from the registry as `w2:compile.rs#build_registered` does; `CompiledFragment::sources(&self) -> Vec<Option<Hash>>` by position.
  - In `gate.rs`: `Layer::Pairing`; `fn pairing(store: &TermStore, frag: &CompiledFragment) -> Result<(), String>` (trusted): every record has a source term (else `NotCovered`: a `PartialApp` callee has no term); each source peels to its record's `arity`; the callee heads of each source, mapped to positions by the registry, equal the `Call` targets of its record's code other than its own (entry to callee and callee to callee). Mismatch: `Rejected(Pairing, ..)`. The multi-entry `NotCovered` route is deleted.
  - `source_fn` gains `Shape::CombinatorCall` at exact arity whose head is closed (no free variables): the head's position from the registry, `SEnv::call(pos, ..)`; the callee's own body through `source_fn`. `build` makes a `ModEntry` per position and passes the registry's callee terms to `cost` (T10's `cost(store, h, callees)`, unchanged).
  - The statement's callee laws are discharged by each callee's closed proof at the module's `fw` (T10 built the mechanism; this task feeds it several entries).

- [ ] **Step 1: Write the failing tests** (in `modules.rs`).
  ```rust
  #[test] fn goal_2_targets_are_accepted()  // twice_inc_5, let_bound_factorial_10, term 23, specialised: Accepted for
                                            // each the MEMBERSHIP column marks S3; jit.apply == eval on samples
  #[test] fn a_callee_wider_than_its_caller_and_the_reverse()
  //   \x. g x 1 2 with g = \a b c. a + b - c, and \a b c. h (a + b + c) with h = \x. x * 2: Accepted
  #[test] fn a_callee_tail_loop_runs_a_million_iterations()     // Review Focus 5: (\n. g n 0) with
  //   g = rec g n acc = if n <= 0 then acc else g (n - 1) (acc + n): jit.apply at 10^6 = n(n+1)/2, stats.compiled 1;
  //   the WAT holds `return_call $c0`
  #[test] fn a_partial_application_callee_is_not_covered()     // a_pap_of_a_self_recursive_combinator: NotCovered
  ```
  Run: `cargo test -p tatic --lib modules`. Expected: FAIL (`NotCovered` for the Goal 2 targets).
- [ ] **Step 2: Implement** the Interfaces.
- [ ] **Step 2b: Retire the tests that pin the multi-entry `NotCovered` route.** Delete `a_module_with_a_callee_is_not_covered_until_s3` from `proof/tests/gate.rs` (its case is `goal_2_targets_are_accepted`'s `twice_inc_5`, or, where `MEMBERSHIP` parked that target for a `Raw` line, `verdicts_match`'s Raw rule). Re-fill `VERDICTS` from T13's print helper, never by hand, then check `git diff -- crates/tatic/src/proof/tests/baseline.rs`: the only moves are `NotCovered` to `Accepted`, and only on rows whose module holds a record other than the entry; any other move, a row turned `Rejected`, or a `Raw`-bearing row turned `Accepted` is a stop. `verdicts_match`'s rules stay unchanged and are the spec's re-run of the fixture's `Raw`-bearing rows (S3). The freeze is over here: T13's freeze held until T14 starts.
- [ ] **Step 3: Run and time.** `cargo test -p tatic --lib modules && cargo test -p tatic --lib baseline && cargo test -p tatic --test golden_wat`. Expected: PASS, no golden differs from T6's. Then `TRUN(bench, s3-targets, "EXE(v08-s3-targets-exe, proof::tests::gate::time_targets --ignored --exact --nocapture)")` (add the Goal 2 targets to `time_targets` and build the copy into folder `v08-s3-targets-exe` untimed first; their printed `cost` now adds the callee terms' source call sites: check the Goal 1 targets' costs are unchanged, since their modules hold one record); record the times in section 27. A Goal 2 target over the budget leaves its goal: a `PARKED.md` entry.
- [ ] **Step 4: Guard loop** (TOUR: `Item::Func`'s source, `pairing`), **commit.**
  ```bash
  git add crates/tatic/src crates/tatic-wasm docs/TOUR.md docs/tier-cycle docs/runs.md PARKED.md
  git commit -m "gate: modules (sources from the registry, the trusted pairing check, closed exact-arity heads in cps); Goal 2"
  ```

### Task 15: S3 Goal 4's module set, O4, the two-callee terms

**Files:**
- Modify: `crates/tatic/src/proof/tests/modules.rs` (past 299 lines of tests it stays a file of its own: test placement applies to inline blocks only)

**Interfaces:**
- Consumes: T11's `forged_rejected`, `rejected_by`; T14's `pairing`, `Layer::Pairing`; the registry spike's two-callee shapes (`w2:proof/tests/gen_real.rs#m2_terms`).

- [ ] **Step 1: Write the tests.**
  ```rust
  #[test] fn call_site_mutants_are_rejected()
  //   per call site of twice_inc_5 and let_bound_factorial_10: a wrong callee index, two arguments swapped, an
  //   argument instruction dropped and one added, a false callee law (the statement's hypothesis for another
  //   position): each Rejected with its observed layer; each whose statement differs forged too
  #[test] fn case_13_controls_are_rejected()   // `call $c0` to `call $f` and Call(0) to Call(n): Rejected with the
  //   observed layer; forged where build gives a statement (a mutant build refuses at Shape is rejected_by alone)
  #[test] fn a_padding_slot_read_is_rejected() // in a callee narrower than fw, local.get of a padding slot: Rejected(Shape)
  #[test] fn a_call_terms_proof_does_not_prove_another_statement() // the tatic-level kernel negative for a call term
  #[test] fn two_callee_terms_prove_in_one_module() // m2's shapes (one callee calling another included): Accepted
  #[test] fn swapped_call_indices_are_rejected()    // on each m2 term: Rejected; forged where build gives a statement
  #[test] fn swapped_registry_entries_are_refused() // records 0 and 1 exchanged with their sources:
  //   Rejected(Pairing) or Rejected(Walk) (the head-and-body check), pinned by the first run
  #[test] fn a_cyclic_registry_is_never_accepted()  // O4: an m2 fragment edited so callee 0 calls 1 and 1 calls 0:
  //   gate(..) is NotCovered or Rejected
  ```
  Run: `RUN(gate, s3-mutants, "cargo test -j 10 -p tatic --lib modules")`. Expected: exit 0 once each layer is pinned; an `Accepted` mutant is a soundness finding: stop and report.
- [ ] **Step 2: Workspace run** `RUN(gate, s3-workspace, "cargo test -j 10 --workspace")`. Expected: exit 0 (Goal 5 holds again; the compile fuzz passes; held-out tests pass).
- [ ] **Step 3: Guard loop, commit.**
  ```bash
  git add crates/tatic/src/proof/tests/modules.rs docs/runs.md
  git commit -m "test: S3's Goal 4 set (call sites, case-13 controls, padding read, pairing swaps, cyclic registry)"
  ```

### Task 16: S4 a toy second instruction table

**Files:**
- Create: `crates/tatic/src/proof/tests/toy_table.rs` (`mod toy_table;`)
- Modify: nothing else in the S4 commit; a schema change the toy needs is its own earlier commit

**Interfaces:**
- Consumes: `Table::new`, `Row`, `Class`, `Entry`, `EnvAccess`, `Item::Func`, `CompiledFragment`, `gate`.
- Produces: `fn toy() -> Table` with rows `const`, `local.get` (as wasm's), `sub` (`Word`, meaning `\x y. add (sub y x) 1`, a meaning no wasm row has), `lt` (`Bit`, as wasm's); hand-built one-entry fragments.

- [ ] **Step 1: Write the tests.**
  ```rust
  #[test] fn the_toy_table_accepts_its_terms()
  //   \a b. a - b with code [local.get 0, local.get 1, sub]; \a b. if a < b then a - b else b with its code: gate(&toy(), ..) == Accepted
  #[test] fn the_toy_table_rejects_its_mutant()   // [local.get 1, local.get 0, sub] for \a b. a - b: Rejected
  ```
  Run: `cargo test -p tatic --lib toy_table`. Expected: PASS (the seam exists since T3).
- [ ] **Step 2: Check the seam.** Run `git diff --stat` before committing. Expected: only `toy_table.rs` and `proof/tests.rs`; no change to `gate.rs`, `machine/`, `machine.rs`.
- [ ] **Step 3: Commit.**
  ```bash
  git add crates/tatic/src/proof/tests/toy_table.rs crates/tatic/src/proof/tests.rs
  git commit -m "test: a toy second instruction table passes straight-line terms through the unchanged gate (S4)"
  ```

### Task 17: Close v0.8

**Files:**
- Modify: `ROADMAP.md`, `docs/proven.md`, doc 15's section 27, `docs/tier-cycle/README.md`, this plan's and the spec's front matter (`status: done`), `PARKED.md`

- [ ] **Step 1: Docs grep for S3/S4's claims.** `rg -n "NotCovered until S3|multi-entry|a non-entry callee|toy" ROADMAP.md PARKED.md docs/TOUR.md docs/proven.md docs/tier-cycle/README.md docs/decisions`; fix ROADMAP's v0.8 line (its "Done when" with run ids; Goal 7's "installs" read as the gate's verdict, for the user to confirm), `docs/proven.md` (the pairing check in the trusted list). Leftovers go to `PARKED.md` first.
- [ ] **Step 2: Guard loop; check** `Get-Process python, cargo -ErrorAction SilentlyContinue` is empty of this session's leftovers.
- [ ] **Step 3: Commit.**
  ```bash
  git add ROADMAP.md PARKED.md docs
  git commit -m "docs: v0.8 recursion once closed (S3, S4 findings; plan and spec done)"
  ```

## End-state fit

| Change | Lives in (task) | Replaces | Deletes |
|---|---|---|---|
| Row schema (`Class`, `Row`), `Table`, the structural classes, the derived constructor order; `K`, `Ins`, `choose`, `shape`/`out_stack`/`well_formed`, the encoders, `prog`/`seq`/`interp`/`meaning` over a table | `tatic-wasm/src/machine.rs` (T3) | those items in `wasm.rs`; `Wasm` by `Machine` | `ctor_ty` leaf arms, the `interp` literal, the count literal, `seq_step` indices, `ifp`'s index |
| The wasm table and its tests; rows' builders and lines | `tatic-wasm/src/wasm.rs`, `ops.rs` (T3) | `Ins::Push`, `Ins::Op`, `Op` | those, `Op::{term, mnemonic, kind}`, the printer's panic arms for them |
| Source pairing by name; class lookup | `PrimOp::name` in `lang/term.rs`; `shape::wasm_table` (T3) | `shape::op_of`, `is_comparison`'s per-op table | `op_of` |
| `conv` memo guard | `tatic-kernel/src/tests/memo.rs` (T2) | `countdown_invariant_is_not_exponential` | that test, `countdown`, `countdown_law`, `Dup` |
| Calls as `Ins::Call(position)`, no wrapper, one `SelfCall` arm, closed direct callees as `Params(0)` | `jit/lower_wat.rs` (T6) | loop wrapper, tail staging, `Raw` call lines, a closed callee's dead `$env` | `$t` locals, staging, `direct_only`'s `env_len > 0` filter, `EnvAccess::None` |
| IR without a tail fact | `jit/ir.rs` (T6) | `SelfCall { tail }` | `tail`, its check, its tests in `ir.rs`, `compile.rs`, `testing/ir_fuzz.rs`, `verify/decompile/tests.rs` |
| `Entry` record (arity, env access, code) | `machine.rs` (T6) | `Item::Func`'s fields | `header` string, `name` |
| Module items with positions and (S3) sources | `jit/compile.rs` (T6, T14) | the name-based `entry()` | nothing further |
| Printer: labels by position, header from the record, the tail rule | `tatic-wasm/src/print.rs` (T6, T7) | `Loop`/`Br` arms | those arms |
| No loop machinery; no fuel | `machine.rs`, `proof/gate.rs` (T7, T9) | `Ins::Loop`, `Ins::Br`, fuel 1 | loop stack, `gate_with`, `strip_loop`, the `Loop` constructor, `fuel`, `loop_law`, `timeout`, `Machine::good` |
| Frame, `local.get` row, opaque memory | `machine.rs` (T9) | parameters as heap cells | the frame-in-heap fold, `Ins::LocalGet`, `Store`, `Load`, `upd`, the store/load check |
| No hand-written machine laws | the generator, per term (T9) | `wasm/laws.rs` | that file, `append`, `ifp`, `spec` |
| Statement builder (trusted), with O3's private `Clauses` | `machine/statement.rs` (T9-T11) | refl `statement` | refl path |
| Generator: return, `choose`/congruence, call | `machine/sim.rs` (T9, T10) | nothing | nothing |
| `Call` class and `MeaningEnv`; `shape_check` over records (calling `well_formed` per record) | `machine.rs` (T10) | the fixed `Wasm { n }` environment | nothing further |
| Gate: `&Table`, `Verdict`, `Layer`, `build`, `CALL_WEIGHT` and `cost`/`call_sites` (source-side), `source_fn`; (S3) `pairing` | `proof/gate.rs` (T3, T10, T12, T14) | `in_fragment`, `Source::cps`'s `unreachable!` arms | `in_fragment`, `tail`, `operand`, those arms |
| Verdict wiring | `jit.rs#prove_install` (T10) | the `in_fragment` branch | that branch |
| Baseline fixture, membership and verdict tables; held-out, mutant, module and toy tests | `proof/tests/{baseline,held_out,gate_mutants,modules,toy_table}.rs` (T1, T6, T11, T13, T14-T16) | nothing | `in_fragment_rejects_the_rest` (cases moved) |
| Deep tail loop test; tail rule's exhaustive wasmtime test | `jit/tests.rs`; `jit/tail_rule_tests.rs` (T6) | nothing | nothing |
| `kernel_verify` model claim | headers of `proof.rs`, `proof/universal.rs`, `jit.rs` (T6) | "the compiled code loops" | nothing |
| Trust doc | `docs/proven.md` (T13, T17) | the `in_fragment` paragraph | its `loop` and `$p0..`-header claims |
| Findings; the weight-fit script | doc 15 sections 26, 27; `docs/runs/<date>/scripts/` (T13, T14) | nothing | nothing |

`machine.rs`, `machine/statement.rs` and `machine/sim.rs` stay under 1000 lines; a split past it is mechanical. Stopgaps: none planned; the transitional `unreachable!` on `Call` in `seq_step` (T6) lives two tasks and dies in T10, and `in_fragment` keeps routing calls to `kernel_verify` until T10, both by the spec's order.

## Calls this plan made that the spec left open

- `Machine<'t> { n, fw, table }` replaces `Wasm { n }`: the machine is backend-independent once it reads a table.
- One constructor per leaf class (today's push/bin/cmp), the row's meaning supplying the operand; the "derived count" is three plus the structural classes.
- A row's `operand` is an `i64` on every `Ins::Row`; 2-to-1 rows carry 0 and `shape` rejects anything else.
- O1 is tried in T10 with `Call`'s meaning, not in T9 (spec S2c step 1 lists it there): a constructor cannot enter `Prog` without an interpretation. Because T9's go/no-go then runs on a machine without `Call`, T10 Step 4b reruns its relational protocol with `Call` in place and stops for the user on a median over 0.57 s (Goal 5's cap floor).
- `Item::Func` carries its position, and `CompiledFragment.entry_pos` names the entry's; a `Pap` wrapper is an `Item::Text` with no record (`records()` gives `None` at its position), and no `CallKnown` targets one (`ir.rs#lifted`).
- S2b's test edits that name the wrapper land in T6 (the commit that stops emitting it), so every commit stays green; T7 deletes the dead variants.
- The membership and verdict columns are separate keyed tables beside `BASELINE`, so S0's rows stay byte-stable.
- Layers the spec does not fix for a mutant are pinned by the first run and named in the test.
