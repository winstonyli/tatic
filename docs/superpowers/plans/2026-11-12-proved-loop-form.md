---
status: active
---

# The proved loop form: implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A gate-covered self-tail-recursive function installs as a wasm `loop` whose text the kernel proved. It is built from two new machine instructions (`Set`, `Br`) and an untrusted loop-form pass in the lowering.

**Architecture:**
- T1: `Set` arrives as a row class.
- T2: `Br` arrives as a structural constructor typed like a call with no arguments (spec O3), with a restart field in `MeaningEnv`; `print.rs` gains a tail-call traversal, which the ported tests use.
- T3: the printer gains the loop wrapper around a body that holds `br $top`.
- T4: an untrusted pass in `lower_wat.rs` rewrites tail `Call(own)` into `Set`s and `Br` using that traversal.
- `sim.rs`, `gate.rs` and the kernel do not change.

**Tech Stack:**
- Rust 2024 workspace.
- `tatic-kernel` (unchanged).
- `tatic-wasm`: `machine.rs`, `machine/statement.rs`, `ops.rs`, `wasm.rs`, `print.rs`.
- `tatic`: `jit/lower_wat.rs`, tests.
- wasmtime 42.0.1.
- `~/.claude/runs/run.ps1`.

**Spec:** `docs/superpowers/specs/2026-11-12-proved-loop-form-design.md`. Its Shapes A and B are binding once approved.
- This plan implements A1 with O3, and B1. The patch to start from is `docs/runs/2026-11-12/patches/o3-br-spike.patch` (on d1c4fed: main's arm rule, `Br` typed like a call, `held_out_b` among the targets); `setbr-spike.patch` is the earlier, terminal-`Br` spike.
- Its `h4_print.rs`, the `pub mod h4_print` line and the WAT-vs-h4 test are scaffolding: do not port them.
- Findings: `docs/tier-cycle/`, "v0.8's build: measurements and checks".

**Where the work runs.** First commit the spec's, this plan's and the tier-cycle doc's current edits on `main` (all are tracked, so a worktree branched before that commit would carry the older versions). Then a worktree branch `proved-loop-form` off `main` at `../tatic-loop` (superpowers:using-git-worktrees). Set `CARGO_TARGET_DIR` to a short path (`C:\wpt\loop`), because the default path hits the linker's length limit for some builds. Never push, tag or merge; the user does that.

## Global Constraints

- `machine/sim.rs`, `proof/gate.rs` and `tatic-kernel` are not edited. If a step seems to need an edit there, stop and report.
- Any test or build over about a minute goes through `run.ps1 -Affinity CFF` (memory-capped). Timed numbers come only from `-Timed` runs.
- Before each commit that touches what they check, these pass: `bash scripts/check/{size_check,test_placement_check,tour_check,cite_check,layout_check,front_matter_check,stack_literal_check,script_header_check,doc_index_check}.sh`.
- `machine.rs` is 765 lines and the O3 patch adds about 70 lines of code, so it stays under the 1000-line limit. Its inline test block is 168 lines, so new machine tests go in a new file, `crates/tatic-wasm/src/machine/loop_tests.rs` (`#[cfg(test)] mod loop_tests;`), which keeps the inline block and the file well under both limits. Run `size_check` and `test_placement_check` anyway.
- `crates/tatic/tests/compile_fuzz.rs` is exactly at its `size_allowlist.txt` cap (1140): it must not grow.
- A thread that runs a gate check deeply uses `tatic_kernel::CHECK_STACK` (the tests' `big` helper does).
- Never let python read stdin: write the script to a file and run `python -P f.py < /dev/null`.
- Commits use explicit pathspecs and end with the session's current `Co-Authored-By` attribution line.
- Stop and report, without working around it, if any of these happens:
  - a list the spec expects `Accepted` is refused (most likely the callee loop, which no spike covered);
  - `baseline.rs`'s `VERDICTS` changes;
  - a ported mutant proves.
- Every commit leaves the workspace compiling. When a new `Ins` variant or a changed signature reaches files outside a task's list, fix them in the same commit and report each one.

## Review Focus

1. A tail self-call inside an `If` arm, where the `If` is not last in the body (`1 + (if c then f(x) else 0)`). Expected: `call`, not `Br`, because the tail rule says it is not tail. Test: T4 Step 1.
2. A module whose callee (not the entry) is self-tail-recursive. Expected: its own `loop $top` wrapper, with `br $top` restarting the callee. Test: T2 Step 1 (callee mutants) and T4 Step 1 (`modules.rs`).
3. A term whose verdict changes because of the pass. Example: a covered term whose loop-form list the walk cannot prove (like the spike's `+ 0` case) stops installing. Expected: `baseline.rs`'s `VERDICTS` table is unchanged. Test: T4 Step 4.
4. `capturing_closure_loop`'s cold JIT time (gate build plus check). Expected: within 1.5x of main's. Test: T5 Step 2.
5. Well-shaped code after a `Br` (`[Br, get 0, add]`, or `[konst 1, Br, add]`, where the dead `add` consumes a surplus word), which `shape` accepts. Expected: it means `restart fr mu` (the code after is ignored), and printed inside an arm it validates under wasmtime, since the stack is polymorphic after `br`. Test: T2 Step 1 (meaning), T3 Step 1 (validation).

---

### Task 1: `Set` and the `local.set` row

**Files:**
- Modify: `crates/tatic-wasm/src/machine.rs`:
  - `Class::Set`;
  - `kind` becomes `push`, plus `takes_operand`;
  - `ctor_list` (to `[Ctor; 6]`) and `built` gain the leaf;
  - `ctor_ty`, `seq_step`, `interp`;
  - `Machine::setter_ty` and `Machine::setter`;
  - `shape`'s operand rule;
  - `shape_check`'s `gets` walk;
  - the module doc (lines 5 to 12: the constructor list, and "locals ... never returned");
  - the `shape_check` doc (lines 122 to 125), which names only `local.get`.
- Modify: `crates/tatic-wasm/src/ops.rs` (`local_set_row`).
- Modify: `crates/tatic-wasm/src/wasm.rs`: the table, the names list and cases array, and the `match row.class` in `wasm_rows_are_closed_and_typed`.
- Modify: `crates/tatic/src/jit/op_table_tests.rs:61,69` (`kind()` becomes `push().expect(..)`).
- Test: `crates/tatic-wasm/src/machine/loop_tests.rs` (new). The gate-level `Set` checks (the slot bound, the no-op prelude) come in T2, where `Set` has a user.

**Interfaces:**
- Produces:
  - `Class::Set`.
  - `impl Class { pub fn pops(self) -> usize; pub fn push(self) -> Option<K>; pub fn takes_operand(self) -> bool }`. `Set` pops 1, pushes `None` and takes an operand, as `Const` does.
  - Row `local.set`, whose operand is the slot; it prints `local.set $p{i}`.
  - `Machine::setter(&self, c: &mut Cx, i: usize) -> Expr` (spike: `setter`, `put`).

- [ ] **Step 0.** Set this plan's and the spec's front matter to `status: active` (commit with Step 4).
- [ ] **Step 1: Failing tests.**
  - `machine/loop_tests.rs` (`#[cfg(test)] mod loop_tests;` in `machine.rs`; make the inline tests' `konst` and `row` helpers, lines 642 to 646, `pub(super)` and import them): `local_set_writes_one_slot`, in the style of `local_get_reads_the_frame`. At `fw` 3, build the frame by hand as a `mkpair` chain of law-bound variables, three slots and the terminal word, as `local_get_reads_the_frame` binds `x[3]` and `x[4]` (`Machine::frame` pads and terminates with literal 0s, which would hide a clobbered word). For each `i` and `j` in {0, 1, 2}, `[get 1, konst 1, add, Set i, get j]` (it leaves one word, so the scaffold's `G [W]` continuation fits) reads the written word when `i == j` and slot `j`'s variable otherwise; `i = 2` reaches `put`'s last-slot case. Build the test's `MeaningEnv` in one helper in `loop_tests.rs`, so T2 adds `restart` in one place.
  - Run it. Expected: it fails at run time (`no row "local.set"`).
- [ ] **Step 2: Implement.**
  - Add the class, the row and the setter, using the spike's hunks for `setter_ty`, `put`, `setter` and `local_set_row`.
  - `seq_step`'s Row arm continues on `with(&[k], pops)` when `row.class.push()` is `Some(k)`, and on `below(pops)` when it is `None`.
  - `shape`'s Row arm pushes `row.class.push()` only when it is `Some`, and its operand rule reads `takes_operand()`.
  - `gets` matches `Ins::Row { name: "local.get" | "local.set", operand }` with the existing bound, and its message becomes `"{name} {operand} is out of the {arity} parameters"`.
- [ ] **Step 3: Verify.** Run the test, then `cargo test -p tatic-wasm` and `cargo test -p tatic op_table`. Expected: pass.
- [ ] **Step 4: Commit.** `tatic-wasm: a Set class and the local.set row (params only); kind() becomes push()`. In the same commit, `docs/TOUR.md` line 41 (the machine's classes) and its glossary gain `Set`; run `tour_check`.

### Task 2: `Br` and the restart field

**Files:**
- Modify: `crates/tatic-wasm/src/machine.rs`:
  - `Ins::Br`, `Ctor::Br`, `MeaningEnv.restart`;
  - `interp(.., calls, restart)` and `meaning`, which thread the field;
  - `ctor_list` (to `[Ctor; 7]`) and `built`;
  - `shape`'s `Br` arm (pushes `W`, with the comment from the O3 patch); `seq_step`'s `Br` arm, which continues into the rest like a `Call` with no arguments;
  - `well_formed`'s doc ("runs and falls through, or restarts at a `Br`") and the module doc's constructor list;
  - the `MeaningEnv` literal in the test at line 707, and T1's helper in `loop_tests.rs`. Port the spike's `restart` built from the law's `kk`: `R` is abstract there, so no closed term fits.
- Modify: `crates/tatic-wasm/src/machine/statement.rs` (`G::bm` fills `restart`).
- Modify: `crates/tatic-wasm/src/print.rs`: `Br` prints `br $top` (the wrapper comes in T3); add `tail_at` and `map_tail_calls`, and `print_body` computes `last_tail` with `tail_at`.
- Modify: `docs/TOUR.md`: line 41 gains `Br` and the restart field, and the glossary gains `Br`; run `tour_check`.
- Test: `crates/tatic/src/proof/tests/loop_form.rs` (new; register `mod loop_form;` in `proof/tests.rs`); `crates/tatic/src/proof/tests/modules.rs` (the callee cases, which need its private `with_record`); `crates/tatic-wasm/src/machine/loop_tests.rs`.

**Interfaces:**
- Consumes: T1's `Class::Set`, `local.set`.
- Produces:
  - `Ins::Br`.
  - `MeaningEnv { r, ch, calls, restart: At }`, with `restart : Fr -> Mem -> R`.
  - `Ctor::Br : Pi A. F (V, A) -> F A`; its meaning `\A rest fr st mu. restart fr mu`.
  - `shape`, `out_stack`, `shape_check` and `well_formed` keep their signatures.
  - `pub fn map_tail_calls(code: &[Ins], f: &mut dyn FnMut(usize) -> Option<Vec<Ins>>) -> Vec<Ins>` in `print.rs`. It replaces each tail-position `Call(j)` of a body with `f(j)` when that returns `Some`, and recurses into both arms of a tail `If`.
  - `fn tail_at(tail: bool, i: usize, len: usize) -> bool`, which both `map_tail_calls` (through a private recursive helper that carries `tail`) and `print_body` use.

- [ ] **Step 1: Failing tests.**
  - `machine/loop_tests.rs`, `br_restarts_on_the_current_frame`. With a stub `restart`, each list below reduces to `restart fr' mu` and has shape `[W]` (so the scaffold's `G [W]` continuation fits):
    - `[konst 1, Set 0, konst 9, Br, add]`: over a hand-built frame of variables (as in T1), `fr'` is that frame with slot 0 equal to 1 and every other slot and the terminal word its variable (compare the whole frame); the 9 under the `Br` and the dead `add` after it are ignored;
    - Review Focus 5: `[Br, get 0, add]` and `[konst 1, Br, add]`, with `fr' = fr`;
    - `[Br]`, with `fr' = fr`.
  - `loop_form.rs`, the ported spike tests:
    - Add `pub(super) fn call_form(code: &[Ins], own: usize, arity: usize) -> Vec<Ins>`. It maps each tail `[Set(arity-1) .. Set(0), Br]` back to `Call(own)`. Add `pub(super) fn call_form_frag(frag: CompiledFragment) -> CompiledFragment`, which applies `call_form` to every `Item::Func` record with that record's own `pos` and `entry.arity` (a loop over `frag.module`, as `modules.rs#with_record` does). `run()` and every target and mutant start from `call_form_frag(compiled ..)`, before any transform. Before T4 it is the identity; after T4 it undoes the pass, so the tests still start from the `Call` form. A wrong `call_form` shows as a target that is not `Accepted` or a mutant at another layer.
    - Port `setbr_targets_are_accepted`, and the spike's `restyle`, renamed `loop_form(code, own, slots)`, as a wrapper over `map_tail_calls` that maps `Call(own)` to `slots`' `Set`s followed by `Br` (the spike's own copy of the tail rule is not ported; every spike call passes `tail = true`, so the parameter goes). T4 moves it into the lowering, where the pass uses it. The 6 targets are the spike's 5 (`capturing_closure_loop` specialised, SUM, SUM2, `partial_application_loop`, `tail_pap`) and `held_out_b` (`test_corpus.rs`), which the O3 spike added and accepted.
    - Port `setbr_mutants_are_rejected`, 54 mutants, from `setbr_spike.rs` in the O3 patch (patch lines 584 to 750), d3 included, with the spike helpers it needs: `rev_slots`, `replace_nth_call`, `strip_call` and `with_code` (`clip` is already `pub(super)` in `gate_mutants.rs`: import it). Port the mutants only (`setbr_mutants_are_rejected` and `strip_call`), not `setbr_wat_matches_h4`, `setbr_gate_time` or `setbr_equal_variants_info`.
    - Expected layers: the O3 patch's table asserts the first spike's layers. Change exactly these 25 rows (`o3-spike-tests`' `err.log` listed them; the run exits 101 on them alone):
      - on each of `capturing_closure_loop`, SUM and SUM2: `(b1)`, `(b2)` and `(b3/g)` Walk to Shape; `(g)` and `(g3)` Shape to Walk (15 rows);
      - factorial: `(c1)` and `(c3)` Walk to Shape; `(c2)` Shape to Walk;
      - fib: the second call's `(c4)` Walk to Shape (the first call's `(c4)` stays Walk); `(c5)` Shape to Walk for both calls;
      - `tail_pap`: `(e1)` and `(e3)` Pairing to Shape; `(e2)` and `(e4)` Walk to Shape.
      - Every other row keeps the patch's layer (`(g2)` and `(g4)` stay Shape). A mutant at another layer is a finding.
  - `loop_form.rs`, `a_mixed_self_call_body_is_accepted`: the term of `gate.rs#gate_accepts_mixed_tail_and_non_tail_calls` (`rec f n acc = .. f (n - 1) (acc + f (n - 1) 0)`, `Accepted` on main), with its tail call restyled, gates `Accepted`. No spike target holds a self-call inside the arguments of the tail self-call; a rejection stops the task, per Global Constraints.
  - `loop_form.rs`, `a_no_op_set_prelude_is_accepted`: SUM's restyled list with `[get 0, Set 0]` prepended gates `Accepted` (the spike asserted this form).
  - `modules.rs`, the callee cases, on its `rec g` term (`\n. (rec g n acc = ..) n 0`, callee `g` at position 0, arity 2), starting from `loop_form::call_form_frag(compiled ..)`:
    - that record with its tail `Call(0)` replaced by `[Set 1, Set 0, Br]` is `Accepted`;
    - three mutants are rejected: the spike's `(f)` shape, `[konst 1, add]` appended after the record's `If` (expected `Walk`), `Set 2` (past the arity: `Rejected(Shape, ..)` with a message that `contains` `local.set 2`), and forward-order `Set`s.
  - `machine/loop_tests.rs`, `a_frame_write_flows_across_the_join`: `[konst 0, konst 1, lt, If([konst 5, Set 0, konst 1], [Br]), get 0, add]`, arity 1, has shape `[W]` and, with `p0 = 2`, means the word 6 (the condition is true, and the then-arm's write is what `get 0` reads after the join).
  - Run them. Expected: they fail to compile (no `Ins::Br`).
- [ ] **Step 2: Implement** per the spec's "Details", using the O3 patch's hunks for `Ctor::Br`, `restart`, `interp`'s `br`, `seq_step`, `shape` and `G::bm`, and its `Br` print arm. `tail_at` and `map_tail_calls` are new code, written from the spec (Details, "Tail rule").
- [ ] **Step 3: Verify.**
  - Run the `loop_form`, `modules` and `machine` tests. Expected: targets, the prelude and the callee are `Accepted`; every mutant is rejected at its expected layer.
  - Run `cargo test -p tatic-wasm print` and `-p tatic --test golden_wat`. Expected: unchanged (`print_body` now calls `tail_at`; `map_tail_calls` has no caller in the printer).
  - Run the workspace suite through the wrapper. Expected: 0 failed.
  - Run `size_check`.
- [ ] **Step 4: Commit.** `tatic-wasm: Br restarts the function on the current frame with the activation's continuation`.

### Task 3: The printer's loop wrapper

**Files:**
- Modify: `crates/tatic-wasm/src/print.rs`: the loop wrapper in `print_func`, and the docs at lines 12 and 31.
- Modify: `docs/TOUR.md` line 41: the printer wraps a body that holds `br $top` in `loop $top`.
- Test: `crates/tatic/src/proof/tests/loop_form.rs`.

**Interfaces:**
- Consumes: T2's `Ins::Br`.
- Produces: `print_func` wraps the body in `loop $top (result i64)` / `end` when the body holds a `Br`.

- [ ] **Step 1: Failing test.** `loop_form.rs`, `dead_code_after_br_validates` (Review Focus 5 printed): `[get 0, konst 0, le, If([get 1], [Br, get 0, add])]` and `[get 0, konst 0, le, If([get 1], [konst 1, Br, add])]`, arity 2, each printed with `print_func` inside `(module .. )`, pass `wasmtime::Module::new`. Run it. Expected: it fails (no loop wrapper, so `br $top` names no label).
- [ ] **Step 2: Implement** the wrapper (body at depth 6).
- [ ] **Step 3: Verify.** Run `cargo test -p tatic-wasm print` and the new test. Expected: pass. The goldens are unchanged, since no lowered list holds `Br` yet.
- [ ] **Step 4: Commit.** `tatic-wasm: the printer's loop wrapper`; run `tour_check` first.

### Task 4: The loop-form pass

**Files:**
- Modify: `crates/tatic/src/jit/lower_wat.rs`: move `loop_form` and `rev_slots` here (Interfaces), call `loop_form` with `rev_slots(arity)` at the end of `Lowering::function`, and update the module doc at lines 8 to 12.
- Modify these tests:
  - `crates/tatic/src/jit/tests.rs`: `a_tail_loop_of_a_million_iterations_installs_and_runs`, lines 783 to 794.
  - `crates/tatic/src/jit/tail_rule_tests.rs`: `tail_rule_prints_both_forms_in_one_body`, lines 142 to 143.
  - `crates/tatic/src/proof/tests/modules.rs`:
    - `a_callee_tail_loop_runs_a_million_iterations`, lines 70 to 79;
    - `call_site_mutants_are_rejected`: its subject gains the `call_form_frag` wrapper (Step 3); counts and comment stay.
  - `crates/tatic/src/proof/tests/gate_mutants.rs`: `self_call_site_mutants_are_rejected` and `no_loop_spike_controls_are_rejected`.
  - The goldens under `crates/tatic/tests/golden/`.
- Modify: `PARKED.md`. Add "Dead env pushes before a loop-form `br`" in this commit, since the stopgap is created here. Trigger: a profile showing the pushes.
- Modify: `docs/TOUR.md`, the tail-rule sentence near line 89 (a tail self-call now lowers to the loop form) and the glossary's loop form and loop-form pass, in this commit: the data flow changes here.

**Interfaces:**
- Consumes: T2's `map_tail_calls` and `Ins::Br`; T1's `local.set`; T3's wrapper.
- Produces:
  - `pub(crate) fn loop_form(code: &[Ins], own: usize, slots: &[i64]) -> Vec<Ins>` and `pub(crate) fn rev_slots(arity: usize) -> Vec<i64>`, moved from `loop_form.rs` (T2) into `lower_wat.rs` in this commit; `loop_form.rs` deletes its copies and imports both (`crate::jit::lower_wat::{loop_form, rev_slots}`).
  - `Lowering::function` ends with `loop_form(&code, own, &rev_slots(arity))`: tail `Call(own)` becomes `(0..arity).rev().map(Set)` followed by `Br`, and other calls are left alone.

- [ ] **Step 1: Failing tests and the updated assertions.**
  - `loop_form_rewrites_only_tail_self_calls`, a unit test in `lower_wat.rs`:
    - On `[.., If([konst 0], [.., Call(0)])]` at position 0 with arity 2, the `Call(0)` becomes `[Set 1, Set 0, Br]`.
    - Review Focus 1: `[konst 1, .., If([konst 0], [.., Call(0)]), row add]` is unchanged.
    - A tail `Call(1)` is unchanged.
    - A tail `Call(0)` inside an `If` nested two levels deep in tail position is rewritten.
  - `loop_form.rs`, `the_shipped_loops_install_in_loop_form` (the ROADMAP v0.9 check): `capturing_closure_loop` and `held_out_b`, compiled with no `call_form_frag`, gate `Accepted`, and `frag.wat()` holds `br $top` and no self `return_call`.
  - `a_tail_loop_of_a_million_iterations_installs_and_runs`:
    - Assert the text holds `br $top` and no `return_call $f`; it still returns `n(n+1)/2`.
    - Delete the `call`-traps control (lines 792 to 794).
    - Replace the comment at line 783 with "The loop form keeps the Wasm stack flat: a million iterations run through `br $top`."
  - `tail_rule_prints_both_forms_in_one_body` (lines 142 to 143) becomes:
    - `assert_eq!(wat.matches("return_call $f").count(), 0)`;
    - `assert_eq!(wat.matches("br $top").count(), 1)`;
    - `assert_eq!(wat.matches("call $f").count(), 1)` (the non-tail call; drop the `- 1`).
    - Update its comment to match.
  - `lower_wat.rs` tests, `env_word_loops_run_and_match_eval`, modelled on `a_directly_called_capturing_combinator_takes_its_captures_as_parameters` (same module, same `instantiate`). These terms are `NotCovered` and the JIT may never install them, so the test runs the text itself instead of going through `JitEngine::apply`:
    - Terms: direct, `\k n. (rec g m acc = if m <= 0 then acc else g (m - 1) (acc + k)) n 0`; through `call_indirect`, `\k n. (rec f i h = if i <= 0 then h n 0 else f (i - 1) h) 1 (rec g m acc = if m <= 0 then acc else g (m - 1) (acc + k))`, where `h` is a closure-typed parameter as in `samples.rs#closure_typed_loop_carried_parameter_loop`.
    - For each: `try_compile`, then find `g`'s record in `frag.records()` (direct: `records()[0]`; indirect: the unique record whose `env` is `Pointer`) and assert its `env` is `EnvAccess::Params(1)` (direct) or `EnvAccess::Pointer` (indirect). If a term lowers to another access, stop and report, with the access it got.
    - Assert `g`'s function text, sliced from `(func $c{pos}` to the next `(func` as the callee test does, holds `br $top` (in the indirect term `f` loops too, so the whole text is not enough). The indirect term allocates an env per call; about 60 calls stay far below one page, so `hp` needs no reset.
    - Instantiate `frag.wat()` and compare `f(k, n)` with `eval::apply_term` for k in {-3, 0, 7} and n in 0..20 and 100 000.
    - It covers the argued part of B1 (env words, scratch locals).
  - `a_callee_tail_loop_runs_a_million_iterations`:
    - Assert the text between `(func $c0` and the next `(func` holds `br $top` and no `return_call $c0`.
    - Assert `wat.matches("return_call $c0").count() == 1`: the entry's call into the callee, which is not a self-call.
    - It stays `Accepted`. Update its doc line.
  - Run them. Expected: they fail.
- [ ] **Step 2: Implement.** Move `loop_form` and `rev_slots` into `lower_wat.rs` (Interfaces) and call `loop_form(&code, own, &rev_slots(arity))` at the end of `Lowering::function` for every function (spec B1).
- [ ] **Step 3: Keep the call-site mutant tests on the `Call` form.** After the pass, the tail self-call sites of `capturing_closure_loop`, the sum loop (`gate_mutants.rs`) and the pap loop (`modules.rs`) are `Set`s and `Br`, so `Call`-site mutators no longer find them. Wrap each test's subject in `loop_form::call_form_frag`: `gate_mutants.rs`'s `Subject` builders and `modules.rs`'s `move || compiled(&**b)` (line 208) become `move || { let (s, h, f) = compiled(..); (s, h, call_form_frag(f)) }`. Counts, layers and arity branches stay as they are; any change is a finding. `gate_mutants.rs`'s doc at lines 245 to 247 gains that the subject is mapped back to the `Call` form. The shipped loop form is covered by the ported mutants (T2).
- [ ] **Step 4: Goldens and verdicts.**
  - Run `UPDATE_GOLDEN=1 cargo test -p tatic --test golden_wat`, then `git diff --stat crates/tatic/tests/golden/` and the full diff.
  - Expected: only self-tail-recursive functions change. Each gains the wrapper lines, has its body re-indented by two, and has its tail call's lines replaced. Non-self `return_call`s stay (`twice_inc_5`, the `a_pap_*` terms, `a_capturing_closure_call`).
  - Expected: 11 goldens change (`capturing_closure_loop` and its `_specialised`, `closure_typed_loop_carried_parameter_loop`, gcd, `gcd_with_two_base_cases`, `inconsistent_arity_loop_carried_parameter_loop`, iterate, `partial_application_loop` and its `_specialised`, and the two `tail_recursive_loop_*` terms). Report the list; any other change is a finding.
  - `gate.rs#gate_accepts_mixed_tail_and_non_tail_calls` now gates the loop form unwrapped; it must stay `Accepted`.
  - Run `baseline.rs`'s verdict test (`VERDICTS`). Expected: unchanged (Review Focus 3; a change stops the task, per Global Constraints).
- [ ] **Step 5: Suite.** Run the workspace suite through the wrapper. Expected: 0 failed.
  - The compile fuzz reaches the loop form by construction: `gen_tail_recursive` always builds a tail self-call and `gen_program` draws it one time in four. Confirm once with a temporary, uncommitted `eprintln!` of the count of programs that ran compiled (`jit.stats.compiled > 0`) and whose text holds `br $top`, report the count, and record it in T5's tier-cycle section. No committed count: `compile_fuzz.rs` is at its size cap and its generators are private to it.
- [ ] **Step 6: Commit.** `jit: the lowering rewrites tail self-calls to the proved loop form`.

### Task 5: Docs, bench, milestone

**Files:**
- Modify: `docs/superpowers/specs/2026-11-10-v08-recursion-once-design.md`: a "Reopened 2026-11-12" line under D1's heading, linking the new spec.
- Modify: `docs/decisions/2026-11-10-v08-shape-and-any-backend.md`: the "loop and br do not survive" line.
- Modify these comments, which say the model's `loop`/`br` stands for the emitted `return_call`:
  - `crates/tatic/src/jit.rs:291-292`;
  - `crates/tatic/src/proof.rs:30-32`;
  - `crates/tatic/src/proof/universal.rs:298`;
  - `crates/tatic/src/jit/ir.rs:78` (`SelfCall`);
  - (`gate_mutants.rs`'s doc at lines 245 to 247 changed in T4.)
- Modify: `crates/tatic-wasm/src/machine.rs:100`, if it states the tail rule.
- Modify: `docs/proven.md`, the gate's claim and its trusted list, at about lines 358 to 382:
  - line 360: self-calls now come as `Call` or, in tail position, as the loop form;
  - the tail-rule bullet: a tail self-call prints as `local.set`s and `br $top`, and `return_call` remains only for calls to other functions;
  - the machine-model bullet: add `local.set` and `br`, and the `shape_check` arity bound they rely on (Constraints in the spec);
  - the scaffolding bullet: the `loop $top` wrapper;
  - the restart field in `G::bm`;
  - the new guards: the definitional tests and `loop_form.rs`.
- Modify: `PARKED.md`:
  - "LocalSet and scratch locals": params-only `Set` is built;
  - "Learned target-cost model": its status line from 1342f07 becomes "parked; Set and Br adopted";
  - the invalid-wasm and h4 lines, if any remain;
- Modify: `docs/tier-cycle/15-the-jit-and-the-target-machine/`: a new section with the results, and its `README.md` index.

- [ ] **Step 1: Docs edits** as listed.
  - Then grep the docs for `return_call` and "no `loop`" and fix each stale claim.
  - `tour_check`, `cite_check`, `doc_index_check` and `front_matter_check` pass.
  - The spec's and plan's `status` become `done`.
- [ ] **Step 2: Bench.** Run `crates/tatic/benches/execution.rs`, branch against main, one `run.ps1 -Kind bench -Timed -Affinity CFF` run per arm, interleaved A B A:
  - `jit_warm_cache_hit` and `jit_cold_compile_and_verify` for `capturing_closure_loop`;
  - `jit_warm_cache_hit` for gcd.
  - Expected: the closure loop's warm call within noise of 4.4 us, and its cold time within 1.5x of main's.
  - If the lease refuses, record the refusal rows, run untimed on `CFF`, say so, and add the timed confirmation to `PARKED.md` with its trigger.
- [ ] **Step 3: Commit.** `docs: the proved loop form (v0.9 work)`.

## End-state fit

The spec's table is the reference for the shipped code; the tasks' Files lists add the test files. In summary:
- `Class` gains `Set`, and `kind` becomes `push` (T1).
- `Br` and the restart field are added; `map_tail_calls`, which the tests and the pass share (T2).
- The loop wrapper is added (T3).
- `lower_wat.rs` gains `loop_form` (T4).
- Removed:
  - `Class::kind`;
  - `return_call $f` for self-calls in printed text;
  - the `call`-traps control;
  - the stale "stands for `return_call`" comments.
- The tail rule stays for calls to other functions.
- New stopgap: the dead env pushes, parked in T4's commit.
