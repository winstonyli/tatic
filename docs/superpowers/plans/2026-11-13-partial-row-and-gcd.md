---
status: active
---

# The partial row, and gcd through the gate: implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `%` becomes a partial wasm row (`mod`, domain `y != 0`) guarded on both sides of the gate, so `gcd` and
`gcd_with_two_base_cases` are `Accepted`, with the table cached in `tatic-wasm` and eval reading the domain through
the row.

**Architecture:** A `Dom { holds, circuit }` on every `Row`; every Word site, machine and source, becomes
`choose(dom x y, rest(op x y), z)` through the walk's probe, `z` the statement's out-of-fuel answer; the walk gains a
last-resort `refl`. The table becomes a `OnceLock` in `tatic-wasm/src/wasm.rs#table`, and `jit/shape.rs#wasm_table`
goes.

**Tech Stack:** Rust workspace (`tatic`, `tatic-wasm`, `church-bv`), the kernel `tatic_kernel`, wasmtime 42 in tests.

**Spec:** `docs/superpowers/specs/2026-11-13-partial-row-and-gcd-design.md` (approved 2026-11-13, e1), cited as
"spec §N". The closest code is the spike patch
`docs/superpowers/spikes/2026-11-13-word-row-guard-on-the-linear-step-spike.patch` ("the patch"; it applies cleanly to
`main` at `b19517d`, checked 2026-11-13). Tasks port its hunks by file. Not ported: everything it marks `SPIKE` (the
code stays, the mark goes), the `DROP_GUARD` thread-local and `spike_drop_guard` (and their callers), `SEnv::guard`
(the two `cps` arms call `e.choose` directly), the `op_table_tests.rs` skip, and `x1_spike.rs` (Task 6 copies its
`chain_src` by hand).

## Global Constraints

- Task 0 commits the spec and this plan as `status: active`; Task 8 sets both `done`.
- Every run over about a minute (church-bv's tests, a whole-crate `cargo test`, `print_verdict_rows`, the ignored
  suites, `p1_probe`, the eval count) goes through `powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1"
  -Kind <kind> -Name <name> -Affinity CFF -Command "<cmd>"`, called from bash, with a watcher on its `run.json`; it
  gets its `docs/runs.md` row. A module-filtered `cargo test` in the edit loop needs neither. Redirect test output to a
  file and read its tail.
- Python, if any script is needed: never read stdin; write the script to a file and run `python -P f.py < /dev/null`.
- Before each commit: `bash scripts/check/size_check.sh` and `bash scripts/check/test_placement_check.sh`
  (`machine.rs` is at 864 lines; an inline `mod tests` block over 299 lines must move out). A commit that names a new
  concept in the tour, or removes or renames an item it cites, edits `docs/TOUR.md` and runs
  `bash scripts/check/tour_check.sh`.
- Commits: explicit pathspecs, `git diff --stat` checked first, the session's attribution trailer. No push, tag or bump.
  A task that launched wrapper runs commits their `docs/runs.md` rows with its own commit.
- Verdicts: only the two gcd rows of `VERDICTS` change (spec "Intent", Done when).
- `MAX_GATE_TREE` and `CALL_WEIGHT` are not refitted (spec §7). `Div` keeps no row and its own zero check (spec "Not in
  scope").

## Review Focus

1. **A Word site the source leaves unguarded** (a `Src::Prim` in a callee's or a loop body's source): both sides must
   guard, or the gate rejects. Pinned by Task 4's callee and loop samples (`Accepted`) and Task 5's source-only
   mutants (`Rejected`).
2. **A negative or `MIN` dividend through `rem_s`:** `(-7) % 2 = -1`, `MIN % -1 = 0`, `x % 1 = 0`. Pinned by the
   ported `rem_s_computes_on_literals_*` tests and `agree`'s `EDGES` (Task 4).
3. **Eval of `%` at b = 0 once its own check goes:** still `Err(DivByZero)`, now from the row's `holds`. Pinned by
   Task 7's eval test and `agree`'s out-of-domain branch (Task 4).
4. **The table rebuilt per call:** every reader goes through the one `OnceLock`. Pinned by Task 1 (`table()` returns
   `&'static Table`; `Table::new` appears only in `wasm.rs`, `toy_table.rs` and the table test's negatives).
5. **A guard inside an `If` condition's operand** (`if a % b == 0 then ..`): both sides wrap the whole `If`. Pinned
   by Task 4's `gcd_is_accepted`.

---

### Task 0: Start

- [ ] **Step 1:** Set `status: active` in the spec and this plan; run `bash scripts/check/front_matter_check.sh` and
  `bash scripts/check/cite_check.sh` (both pass). Commit both files ("docs: the partial-row spec and plan, active").

### Task 1: The table, cached in `tatic-wasm`

Place: `tatic-wasm/src/wasm.rs#table` owns the one table; `jit/shape.rs` loses `wasm_table` (spec §2).

**Files:**
- Modify: `crates/tatic-wasm/src/wasm.rs`, `crates/church-bv/src/job.rs` (`PROCESS_WIDE`, line 689),
  `crates/tatic/src/jit/shape.rs` (delete `wasm_table` and its doc; `is_comparison` calls `table()`), `docs/TOUR.md`
  (line 184 cites `shape.rs#wasm_table`), `PARKED.md` (line 514 names `shape::wasm_table`)
- Modify: every caller and mention. Recount first: `git grep -n "wasm_table" -- crates` (69 occurrences in 16 files on
  2026-11-13, code and comments, e.g. `lower_wat.rs:434`'s expect string, `term.rs:27`, `gate.rs:5`) and
  `git grep -n "wasm::table()" -- crates/tatic-wasm/src`.

**Interfaces:**
- Produces: `tatic_wasm::wasm::table() -> &'static Table` (`static TABLE: OnceLock<Table>`, built on first call).

- [ ] **Step 1: Implement** `table()` over `static TABLE: std::sync::OnceLock<Table>` with `get_or_init(||
  Table::new(vec![..]))`, the row list unchanged. If `Table` is not `Sync` (its rows are `&'static str`, a `Class`
  and `fn` pointers, so it should be), stop and report.
- [ ] **Step 2: Move every caller.** `tatic`: `wasm_table()` and `crate::jit::shape::wasm_table()` →
  `tatic_wasm::wasm::table()`. `tatic-wasm`: `let t = crate::wasm::table(); .. table: &t` becomes `table: t`. Every
  comment and string naming `wasm_table` names `wasm::table` (the "no row" wording stays until Task 4). TOUR line
  184: delete the `shape.rs#wasm_table` cite (`wasm.rs#table` is already there); PARKED line 514 names `wasm::table`.
- [ ] **Step 3: Check.** `cargo build -p tatic --all-targets` and `cargo build -p tatic-wasm --all-targets` compile;
  `git grep -n "wasm_table" -- crates docs/TOUR.md PARKED.md` prints nothing; `git grep -nw "Table::new" -- crates`
  shows only `wasm.rs` and `toy_table.rs` (`op_table_tests.rs` joins them in Task 4); `tour_check.sh` passes; `cargo test -p tatic-wasm` and `cargo test -p tatic
  -- proof:: jit::` pass with the counts they had before the task.
- [ ] **Step 4: church-bv's guard.** Add `("../tatic-wasm/src/wasm.rs", "TABLE", "the wasm table: built once, pure")`
  to `PROCESS_WIDE` (declared length 9 → 10); one wrapper run, `-Kind probe -Name t1-hidden -Command "cargo test -p
  church-bv hidden_state_is_classified"`. Expected: PASS. (The guard failing on an unlisted static is its own tested
  behaviour; the spec §2 entry is the only change.)
- [ ] **Step 5: Commit** ("wasm: the table cached in tatic-wasm (OnceLock); shape::wasm_table deleted").

### Task 2: `Dom` on every row

Place: `Dom` in `tatic-wasm/src/ops.rs`, `dom_true` in `encoding/gates.rs` (spec §1).

**Files:**
- Modify: `crates/tatic-wasm/src/ops.rs` (`Dom`, `circuit_row!`'s optional domain, `dom: Dom::TOTAL` on the three
  hand-built rows), `crates/tatic-wasm/src/encoding/gates.rs` (`dom_true` from the patch),
  `crates/tatic-wasm/src/machine.rs` (`Row.dom`, `#[derive(Clone, Copy)]` on `Row`), `crates/tatic-wasm/src/wasm.rs`
  (imports `Dom`; its test), `docs/TOUR.md` (glossary: `Dom`, a row's domain)
- Modify: `crates/tatic/src/proof/tests/toy_table.rs` (`as_wasm` is `*table().row(name).unwrap_or_else(..)`; `toy()`'s
  `sub` takes `dom: Dom::TOTAL`), and any other `Row {` literal `git grep -n "Row {" -- crates` finds

**Interfaces:**
- Produces: `tatic_wasm::ops::Dom { pub holds: fn(i64, i64) -> bool, pub circuit: fn(usize) -> Expr }`, `Clone +
  Copy`, with `Dom::TOTAL` (`holds` always true, `circuit: dom_true`); `Row.dom: Dom`; `encoding::dom_true`;
  `circuit_row!(name, class, build, line)` (domain `$crate::ops::Dom::TOTAL`) and `circuit_row!(name, class, build,
  line, dom)`.

- [ ] **Step 1: Write the failing type test.** In `wasm.rs#wasm_rows_are_closed_and_typed`, per case:
  `infer(&Ctx::new(), &constant_n(row.dom.circuit, n))` is `def_eq` to `arrow(v, arrow(v, bv_ty(1)))`, message
  `"{name}: domain has the wrong type"` (kept beside Task 4's domain loop: it holds from this task on, before any row
  has a non-trivial domain). Run `cargo test -p tatic-wasm -- wasm_rows`. Expected: compile error (no
  `dom`).
- [ ] **Step 2: Implement** `Dom`, `dom_true`, `Row.dom`, `Row: Clone + Copy`, the macro's 5-argument arm, `TOTAL` on
  `const_row`/`local_get_row`/`local_set_row` (nothing reads it there). `Row`'s doc: `dom` is where the row has a
  value, read only at Word sites. TOUR: `Dom` in the glossary.
- [ ] **Step 3: Run** `cargo test -p tatic-wasm` and `cargo test -p tatic -- proof::tests::toy_table`; `tour_check.sh`.
  Expected: PASS.
- [ ] **Step 4: Commit** ("wasm: a domain on every row (Dom), constant true on all of them").

### Task 3: The guard on every Word site, and `refl` in the walk

Place: machine `machine.rs#interp`/`ctor_ty`/`seq_step`; statement `machine/statement.rs`; source `proof/gate.rs#cps`
and its copy `machine/sim/tests.rs#cps`; walk `machine/sim.rs#Sim::sim_step` (spec §5). No partial row yet: every
guard is `choose(1, rest, z)`, so no verdict moves.

**Files:**
- Modify: `crates/tatic-wasm/src/machine.rs` (the patch's hunk, with `seq_step` passing `constant_n(row.dom.circuit,
  self.n)`), its test `local_get_reads_the_frame` (builds a `MeaningEnv` near line 806),
  `crates/tatic-wasm/src/machine/loop_tests.rs` (`meaning_env` and its three callers, lines 73, 128, 178)
- Modify: `crates/tatic-wasm/src/machine/statement.rs` (the patch's hunk without `guard`: `SEnv.z`, `bm`/`bs` take
  `z`, `bm_bs` passes `self.z`), `crates/tatic-wasm/src/machine/sim.rs` (the `refl` hunk),
  `crates/tatic/src/proof/gate.rs` and `crates/tatic-wasm/src/machine/sim/tests.rs` (`cps`'s `Prim` arm as in the
  patch, reading `.dom.circuit`, with `e.choose(c, app2(dom, x, y), kk, c.at(e.z))` in place of `e.guard(..)`),
  `docs/TOUR.md` (the data flow: every Word site a guarded choice; the walk's `refl`)
- Modify, docs that state the Word constructor's type: `machine.rs`'s `Row`/`Class` docs (lines 55-56, 90-92), the
  `ctor_ty`/`ctor_list` docs and the module doc; `proof/gate.rs`'s module doc (both sides guard Word sites through
  the table's `dom`).

**`z` is `At`, not `Option<At>`** (spec §5), the one place the port departs from the patch: `binop`'s guarded leaf is
`pick(c, dom x y, kk, c.at(z))` with no `map_or` fallback, and returns `kk` only when `!guarded`. The hand-built envs
supply a real `z` (below), so they now exercise the guard: a test there that changes is a finding, not noise.

**Interfaces:**
- Consumes: `Row.dom.circuit` (Task 2).
- Produces: `MeaningEnv { r, ch, z: At, calls, restart }`; `SEnv.z: At`; `G::bm(&self, c, r: At, z: At, ch, ..)`,
  `G::bs(&self, c, r: At, z: At, ch, ..)`.

- [ ] **Step 1: Machine, statement and source.** Port the hunks as listed. The hand-built envs: append an `R`-typed
  binder as the last entry of each test's telescope (so no existing `x[i]` moves), pass it as a new `z: At` parameter
  of `meaning_env` and into `local_get_reads_the_frame`'s `MeaningEnv`.
- [ ] **Step 2: Run the walk's tests without `refl` (RED).** `cargo test -p tatic-wasm -- machine::sim`. Expected:
  every case with a Word site fails with "the machine .. but the source .." at a guard's else (`z` against `z`); cases
  without one pass. Any other failure: stop and debug.
- [ ] **Step 3: Port the `refl` hunk** (last in `sim_step`). Expected: `machine::sim` PASS.
- [ ] **Step 4: Run** `cargo test -p tatic-wasm` and `cargo test -p tatic -- proof:: jit::`. Expected: PASS, the
  `baseline` verdict tests and the three linear-work tests included (`gate_check_work_is_linear_in_the_tree`,
  `gate_build_work_is_linear_in_the_tree`, `gate_check_work_is_linear_in_an_if_chain`). TOUR edit; `tour_check.sh`;
  `size_check` on `machine.rs`.
- [ ] **Step 5: Commit** ("gate: every Word site guarded through the probe on both sides; refl closes equal sides").

### Task 4: The `mod` row, and gcd through the gate (stop point)

Place: the row in `wasm.rs#table`, its circuit in `encoding/gates.rs`; the lowering arm in `jit/lower_wat.rs#node`;
the table test in `jit/op_table_tests.rs` (spec §2, §4, §6). If `gcd_is_accepted` fails after Step 3, stop and report
(spec §6, first task).

**Files:**
- Modify: `crates/tatic-wasm/src/encoding/gates.rs`, `crates/tatic-wasm/src/encoding/tests.rs` (the patch's hunks:
  `nonzero_second`, `rem_s`, `neg_if`, `rem_s_bits`, `rem_ref`, the three `rem_s_computes_on_literals_*` tests, n8
  exhaustive `#[ignore]`d), `crates/tatic-wasm/src/ops.rs` (`Dom::NONZERO_SECOND`), `crates/tatic-wasm/src/wasm.rs`
  (row after `mul`, `names()`, `cases` 11 → 12, module doc), `crates/tatic/src/jit/lower_wat.rs` (delete the
  `PrimOp::Mod => raw(w, "i64.rem_s")` arm), `crates/tatic/src/lang/term.rs` (line 27's "`div` and `mod` have no
  row" → only `div`), `docs/TOUR.md` (the partial row)
- Modify: `crates/tatic/src/proof/tests/gate.rs` (`gcd_is_accepted`; drop "gcd (Mod)" from
  `what_cps_cannot_take_is_not_covered`), `crates/tatic/src/proof/tests/modules.rs` (the callee sample),
  `crates/tatic/src/proof/tests/loop_form.rs` (`the_shipped_loops_install_in_loop_form`),
  `crates/tatic/src/proof/tests/baseline.rs#VERDICTS`, `crates/tatic/src/proof/tests/gate_mutants.rs` (the carrier)
- Modify: `crates/tatic/src/jit/op_table_tests.rs` (`agree(t: &Table, ..)`, the domain branches, the domain loop, two
  negatives, `every_prim_op_with_a_row_names_it`, header and the "six non-`Div`/`Mod`" doc)

**Interfaces:**
- Consumes: `table()` (Task 1), `Dom`, `Row: Copy` (Task 2), the guard (Task 3).
- Produces: `Dom::NONZERO_SECOND` (`holds: |_, y| y != 0`, `circuit: nonzero_second`); `encoding::{rem_s,
  nonzero_second}`; the row `circuit_row!("mod", Class::Word, rem_s, "i64.rem_s", Dom::NONZERO_SECOND)`; `agree(t:
  &Table, n: usize, pairs: ..)`.

- [ ] **Step 1: Write the failing gate test** `gcd_is_accepted` in `proof/tests/gate.rs`, in the shape of
  `loop_form.rs#the_shipped_loops_install_in_loop_form` (`big`, `compiled`, `gate(tatic_wasm::wasm::table(), ..)`,
  `assert_eq!(v, Verdict::Accepted, "{name}")`) over `samples::gcd`, `samples::gcd_with_two_base_cases` and
  `source(s, r"\a b. if a % b == 0 then a else b")`. Run it. Expected: FAIL, `NotCovered`.
- [ ] **Step 2: Port the encoding hunks; add `NONZERO_SECOND` and the row; drop the lowering arm;** `wasm.rs`'s test:
  `"mod"` after `"mul"` in `names()`, `("mod", 0)` in `cases` (12 entries); module doc "the word rows `add` `sub` `mul`
  `mod`". Run `cargo test -p tatic-wasm -- rem_s_computes wasm_rows`. Expected: PASS.
- [ ] **Step 3: Run** `gcd_is_accepted`. Expected: PASS. Else stop and report the verdict and the walk's message.
- [ ] **Step 4: Off the tail call.** In `modules.rs`, beside `a_callee_wider_than_its_caller_and_the_reverse`, test
  `a_callee_holding_mod_is_accepted`: `raw_verdict(|s| source(s, r"\a b. (\x y. x % y) (a + 1) b"))` has `records > 1`
  and is `Accepted` (unspecialised: the specialiser would inline the callee). In `loop_form.rs`, the `shipped` array of
  `the_shipped_loops_install_in_loop_form` (declared `[(&str, Build); 2]`, so its length goes to 4) gains `gcd` and `\n. (rec g n acc = if n <= 0 then acc % 7 else g (n - 1)
  (acc + n)) n 0` (`%` in the loop's base leaf, outside the tail call's arguments): each `Accepted`, `br $top` in the
  WAT, no self `return_call` (spec §6, loop_form). Expected: PASS.
- [ ] **Step 5: Flip what the row flips.** Drop "gcd (Mod)" from `what_cps_cannot_take_is_not_covered` (keep "a / b"
  and "a / 0"). `gate_mutants.rs`'s carrier map gains `"mod" => Some("gcd")` (else
  `every_row_has_an_operator_swap_mutant` panics "no carrier for the row mod"); run it: `mul -> mod` and `mod -> add`
  `Rejected` at the walk. Wrapper run `-Kind probe -Name t4-verdicts -Command "cargo test -p tatic print_verdict_rows
  -- --ignored --nocapture"`, diff its rows against `VERDICTS`: exactly the two gcd rows become `Accepted`; write them.
  `every_prim_op_with_a_row_names_it`: only `Div` lacks a row (doc "every source operator but `Div` has a row").
- [ ] **Step 6: Write the failing `agree` negatives** in `op_table_tests.rs`, each at width 8 on the one pair `(5, 0)`
  over `fn with_mod_dom(d: Dom) -> Table`, which copies every row of `table()` into `Table::new` with `mod`'s `dom`
  replaced:
  - `agree_catches_a_domain_on_the_wrong_operand`: `#[should_panic(expected = "wasm disagrees with the domain")]`,
    `Dom { holds: |x, _| x != 0, ..Dom::NONZERO_SECOND }` (`holds` says in domain, wasmtime traps).
  - `agree_catches_a_domain_circuit_that_is_not_holds`: `#[should_panic(expected = "domain circuit is not holds")]`,
    `Dom { circuit: dom_true, ..Dom::NONZERO_SECOND }`.

  Expected: compile error (`agree` takes no table).
- [ ] **Step 7: Implement `agree(t, n, pairs)`** as spec §6 says; rows and `circuit`'s `Machine.table` come from `t`,
  `try_compile` and eval from `table()`, callers pass `table()`. The one ordering the negatives need: wasmtime is
  called first on every pair, before eval (today eval's `.expect` runs first, and at `(5, 0)` it would panic before
  wasmtime under the wrong-operand `holds`); an in-domain trap panics with "wasm disagrees with the domain". Out of
  domain the trap is matched by `downcast_ref::<wasmtime::Trap>()` against `IntegerDivisionByZero` (if wasmtime
  42.0.1 names it otherwise, use the compiler's and say so in the commit). The domain loop runs after the `lt_u`
  block, over every row of `t.names()`, and panics with "domain circuit is not holds".
- [ ] **Step 8: Run** `cargo test -p tatic -- jit::op_table_tests` (both negatives meet their `should_panic`). TOUR:
  the partial row; `tour_check.sh`. Then one wrapper run, `-Kind gate -Name t4-full -Command "cargo test -p tatic-wasm
  && cargo test -p tatic"`. Expected: PASS.
- [ ] **Step 9: Commit** ("wasm: the mod row (rem_s, domain y != 0); gcd and gcd_with_two_base_cases Accepted").

### Task 5: The walk's controls on the guard

Place: the walk's own tests, `machine/sim/tests.rs` (spec §6).

**Files:**
- Modify: `crates/tatic-wasm/src/machine/sim/tests.rs`

**Interfaces:**
- Consumes: `SEnv::choose` (Task 3); `Ctxt::new`, `Ctxt::real`, `widen`, `nat2_lit` (reachable from
  `machine::sim::tests`: `Ctxt` and `widen` are `pub(super)` in `machine::statement`).
- Produces: `run_with(n, arity, code, mk: &(dyn Fn(&Machine) -> Box<SrcFn<'_>> + Sync))`; `run(n, &Case)` stays as
  its caller with a `cps` builder, so no existing call site changes.

- [ ] **Step 1: `run_with`.** The `Machine` is built inside the `CHECK_STACK` thread, so `run_with` takes `mk` and
  calls it there; `run`'s body moves into it. Run `machine::sim`. Expected: PASS (refactor).
- [ ] **Step 2: The `%` case and two source-only mutants.** Add `fn rem() -> Case` returning `("a % b", 2, vec![get(0), get(1),
  row("mod")], pr("mod", Param(0), Param(1)))` and put `rem()` in `prove_accepts_straight_line_and_if`'s array (beside
  `minus()`, `branch()`). New test
  `prove_refuses_a_wrong_guard`: two builders for the same code, each marking `y`, computing `kk = k(c, app2(op, x,
  y))` first, then calling `e.choose` directly: (a) condition `lit(1, 1)` in place of `dom x y`, else `c.at(e.z)`; (b)
  condition `dom x y`, else `kk` (the guard vacuous). Each `run` is `Err` (print the message). Expected: PASS. A
  mutant that is accepted is a hole in the walk: stop and report.
- [ ] **Step 3: The `z` pin** `out_of_domain_answers_z`: build `\a b. a % b`'s source side directly. In a
  `tatic_kernel` telescope over `R : Sort0`, `z : R`, `a : V`, `ks : V -> R`, with `w = widen(&machine, &module)`
  (the machine needs the frame width for `local.get`), `Ctxt::new(c, w, &module, fuel, r, z)` at `fuel =
  c.mark(nat2_lit(2))` as `statement_with`'s unquantified branch builds it; apply `.real(c, 0).sc` to `a`, `lit(n, 0)`
  and `ks`; `whnf` of that is `def_eq` to `z`'s variable. RED check: with this file's `cps` guard else changed to `kk`,
  the test fails; revert.
- [ ] **Step 4: Run** `cargo test -p tatic-wasm`; `test_placement_check` (the file is 249 lines today). Commit
  ("gate: the guard's controls: source-only mutants and the z pin").

### Task 6: Linear work on `%` chains, and the cost re-check

Place: `proof/tests/gate.rs`, beside `gate_check_work_is_linear_in_an_if_chain` (spec §6, §7).

**Files:**
- Modify: `crates/tatic/src/proof/tests/gate.rs`

**Interfaces:**
- Produces: `fn assert_linear(name: &str, src: fn(usize) -> String)` (today's `if_chain_work` body inline, over depths
  16, 32, 64; all accepted; check and build each under 2.2x per doubling, the if-chain test's assertions).

- [ ] **Step 1: Refactor:** `if_chain_work(d)` becomes `if_chain_src(d) -> String`;
  `gate_check_work_is_linear_in_an_if_chain` becomes `assert_linear("if chain", if_chain_src)`. Run it. Expected:
  PASS, the same numbers as before.
- [ ] **Step 2: Add** `gate_work_is_linear_in_a_mod_chain`: `assert_linear` over `right_mod_chain` (the patch's
  `x1_spike.rs#chain_src`, copied: seed `"b"`, then `e = format!("({} % {e})", if k % 2 == 0 { "a" } else { "b" })`)
  and `left_mod_chain` (seed `"b"`, then `e = format!("({e} % {})", if k % 2 == 0 { "a" } else { "b" })`), each
  wrapped `\a b. {e}`. Expected: PASS (the spike measured the right chain's check at 1.02x to 1.47x; its build and the
  left chain are first measured here; a failure is a finding to report with its numbers).
- [ ] **Step 3: Cost re-check.** Paste the patch's `p1_probe` into `gate.rs` uncommitted (`wasm_table()` →
  `tatic_wasm::wasm::table()`), one wrapper run `-Kind probe -Name t6-p1 -Command "cargo test -p tatic p1_probe --
  --ignored --nocapture"`, and compare with spec §7's "this design" column. A figure more than 20% off is investigated
  before the plan closes, starting with Task 3's `z: At` change; a fix lands in Task 3's code with its own commit.
  Remove the probe; its numbers and run id go into Task 8's doc section.
- [ ] **Step 4: Commit** ("gate: % chains are linear, left and right nested").

### Task 7: Eval reads the domain through the row

Place: `tatic/src/lang/eval.rs#apply_prim` (spec §3).

**Files:**
- Modify: `crates/tatic/src/lang/eval.rs` (lookup before the match; delete `Mod`'s zero check, lines 146-151 on
  2026-11-13; `Div`'s stays), its tests (`mod tests`, line 177)

**Interfaces:**
- Consumes: `table()` (Task 1), `Row.dom.holds` (Task 2), the `mod` row (Task 4).

- [ ] **Step 1: Count before.** Add an `#[ignore]`d probe test `eval_prim_heavy_count` in `eval.rs`'s `mod tests`
  (uncommitted): `apply_term` on the `fib` sample at an argument that runs 0.2-2 s (start at 22). Build the lib test
  exe (`cargo test -p tatic --lib --no-run`, path from its output), copy it outside `target` (into the run folder),
  and count: `icount.ps1 -Exe <copy> -Runs 3 -ExeArgs lang::eval::tests::eval_prim_heavy_count,--ignored,--exact`
  (`--exact` needs the full path; ICOUNT.md: best of 3; check the count is the workload's size, not a start-up's).
- [ ] **Step 2: Write the failing test.** Beside the division-by-zero test: `\a b. a % b` at `(5, 0)` is
  `Err(EvalError::DivByZero)` and at `(-7, 2)` is `Ok(-1)`. Delete `Mod`'s own check and run it. Expected: FAIL at
  `(5, 0)`.
- [ ] **Step 3: Implement:** `if let Some(r) = tatic_wasm::wasm::table().row(op.name()) { if !(r.dom.holds)(x, y) {
  return Err(EvalError::DivByZero) } }` before the match, with a comment that `Div` keeps its own check (no row).
  Expected: PASS.
- [ ] **Step 4: Count after,** same steps on the new exe. If the count rises more than 2%, stop and bring the
  numbers with a Decide on indexing rows by `PrimOp` (spec §3); else the by-name lookup stays. Remove the probe test;
  the counts go into Task 8's doc section.
- [ ] **Step 5: Run** `cargo test -p tatic -- lang:: jit::op_table_tests`. Commit ("eval: the row's domain decides %
  by zero; Mod's own check deleted").

### Task 8: The ignored suites, then the docs

Place: as the spec's End-state fit, "Docs, in full".

**Files:**
- Modify: `PARKED.md`, `ROADMAP.md` (line 71), `docs/decisions/2026-11-10-v08-shape-and-any-backend.md`,
  `docs/tier-cycle/15-the-jit-and-the-target-machine/28-the-proved-loop-form-measurements.md` (line 92 cites the
  PARKED section this task deletes), a new `docs/tier-cycle/15-the-jit-and-the-target-machine/32-the-partial-row-and-gcd-through-the-gate.md`
  and its bullet in `docs/tier-cycle/README.md` (after line 66), the comments Step 2's grep finds (the spec's "Docs,
  in full" lists them), the spec and this plan (`status: done`)

- [ ] **Step 1: The suites, once,** each a wrapper run (`-Kind gate`):
  - `cargo test -p tatic-wasm -- --include-ignored`;
  - `cargo test -p tatic -- proof:: --include-ignored --skip measure_cachegrind --skip measure_stack_2mb --skip print_`
    (`measure_cachegrind` needs `GATE_D`; the `print_` tests only print);
  - `cargo test -p tatic measure_stack_2mb -- --ignored` alone (it measures the stack);
  - `cargo test -p tatic -- jit::op_table_tests --ignored` (the exhaustive and all-edges `agree` runs, now over `mod`);
  - `cargo test -p tatic && cargo test -p church-bv` (Tasks 5-7 landed after Task 4's full run).

  Expected: all pass. A failure is debugged to its cause and fixed with a failing test first, in the task that owns
  the code.
- [ ] **Step 2: Grep for drift:** `git grep -n "wasm_table\|no row\|Div/Mod\|Div\`/\`Mod\|partial row and gcd\|rem_s" --
  crates docs ROADMAP.md PARKED.md ':!docs/runs' ':!docs/superpowers/spikes'`; fix each live mention (dated sections
  stay as history, but a cite in one must still resolve: doc 28's line 92 points at section 32).
- [ ] **Step 3: Write** section 32, "The partial row and gcd through the gate (2026-11-13)": the verdicts, `p1_probe`
  against spec §7, the `%` chains' numbers, eval's counts, the run ids; its bullet in the README.
- [ ] **Step 4: PARKED, ROADMAP, decision file.** PARKED: delete "The partial row and gcd"; add three entries, each
  with what, why parked, trigger, evidence and status `parked` (VERSIONING): "Div as a partial row" (why: its
  `MIN / -1` wrap needs the lowering's wrapping sequence modelled as instructions, spec "Not in scope"; trigger: a
  target that divides; includes rows carrying concrete semantics so `apply_prim`'s match goes; evidence:
  `lower_wat.rs#emit_wrapping_div`, `eval.rs#apply_prim`), "Fold total-row guards" (why: by decision, option 1;
  trigger: the gate's check time on Word-heavy programs matters; evidence: the fold spike patch and doc 15's sections
  30 and 31), "Guard Bit sites" (why: every Bit row is total today; trigger: the first partial Bit row; evidence:
  `machine.rs#interp`'s `binop`). ROADMAP line 71: "No milestone
  is open. Candidates are in `PARKED.md`." Decision file: "Open: where the domain lives" becomes decided, linking the
  spec; `git grep -n "where the domain lives"` and fix each mention of the old heading.
- [ ] **Step 5: Check and commit.** `cite_check.sh`, `tour_check.sh`, `front_matter_check.sh`, `layout_check.sh`,
  `doc_index_check.sh`; spec and plan `status: done`. Commit ("docs: the partial row and gcd through the gate").

## End-state fit

| Change | Target | Replaces | Deletes |
|---|---|---|---|
| table cache | `tatic-wasm/src/wasm.rs#table` (`OnceLock`); church-bv `job.rs#PROCESS_WIDE` | `jit/shape.rs#wasm_table` | `wasm_table` and its doc |
| `Dom`, `dom_true` | `tatic-wasm/src/ops.rs`, `encoding/gates.rs` | nothing | nothing |
| `Row.dom`, `Row: Copy` | `tatic-wasm/src/machine.rs#Row` | `toy_table.rs#as_wasm`'s field-by-field copy | that copy |
| `z: At`, Word guard, `refl` | `machine.rs#interp`/`ctor_ty`/`seq_step`, `machine/statement.rs#SEnv`/`G`, `machine/sim.rs#Sim::sim_step` | the unguarded Word leaf | `interp`'s `Option` operand in `shape` |
| source guard | `proof/gate.rs#cps`, `machine/sim/tests.rs#cps` | unguarded `Src::Prim` | nothing |
| `mod` row, `rem_s`, `NONZERO_SECOND` | `wasm.rs#table`, `encoding/gates.rs`, `ops.rs` | lowering's raw `i64.rem_s` | that arm in `lower_wat.rs#node` |
| `agree(&Table)` with the domain | `jit/op_table_tests.rs` | `agree`'s "no division" and "no trap" expects | those expects |
| eval reads `dom.holds` | `lang/eval.rs#apply_prim` | `Mod`'s zero check | that check |
| tests | `op_table_tests.rs`, `encoding/tests.rs`, `wasm.rs`, `machine/sim/tests.rs`, `proof/tests/{gate,gate_mutants,modules,loop_form,toy_table,baseline}.rs` | "gcd (Mod)" in `what_cps_cannot_take_is_not_covered`; `if_chain_work` | that case; `if_chain_work` (into `assert_linear`) |
| docs | TOUR (Tasks 1-4), PARKED, ROADMAP, decision file, doc 15 (28, new 32, README), the comments | stale wording | PARKED's "The partial row and gcd" |

Nothing of the spike survives as scaffolding (see the Spec line); `p1_probe` and the eval count probe are never
committed. No stopgap is parked by this plan.
