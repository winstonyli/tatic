---
status: draft
---

# The proved loop form: implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A gate-covered self-tail-recursive function installs as a wasm `loop` whose text the kernel proved. It is built from two new machine instructions (`Set`, `Br`) and an untrusted loop-form pass in the lowering.

**Architecture:**
- T1: `Set` arrives as a row class.
- T2: `Br` arrives as a structural constructor with a restart field in `MeaningEnv`, and `shape` learns that `Br` ends a path.
- T3: the printer gains the loop wrapper, `br $top` and one shared tail traversal.
- T4: an untrusted pass in `lower_wat.rs` rewrites tail `Call(own)` into `Set`s and `Br` using that traversal.
- `sim.rs`, `gate.rs` and the kernel do not change.

**Tech Stack:**
- Rust 2024 workspace.
- `tatic-kernel` (unchanged).
- `tatic-wasm`: `machine.rs`, `machine/statement.rs`, `ops.rs`, `wasm.rs`, `print.rs`.
- `tatic`: `jit/lower_wat.rs`, tests.
- wasmtime 42.0.1.
- `~/.claude/runs/run.ps1`.

**Spec:** `docs/superpowers/specs/2026-11-12-proved-loop-form-design.md`. Its Shapes A and B are binding once approved. Held for the O3 spike (spec, "Open items"): if it passes, T2 is revised to O3 before any task starts.
- This plan implements A1, the spiked shape, and B1. The spike to start from is `docs/runs/2026-11-12/patches/setbr-spike.patch`.
- Its `h4_print.rs`, the `pub mod h4_print` line, `setbr_review.rs` and the WAT-vs-h4 test are scaffolding: do not port them.
- The spike's `shape` hunk predates e5e9771's arm rule (each `If` arm runs from an empty stack). Port the rule from main, not the hunk.
- Findings: `docs/tier-cycle/`, "v0.8's build: measurements and checks".

**Where the work runs.** First, once the user approves, commit the spec and this plan on `main` (they are untracked drafts, so a worktree would not have them). Then a worktree branch `proved-loop-form` off `main` at `../tatic-loop` (superpowers:using-git-worktrees). Set `CARGO_TARGET_DIR` to a short path (`C:\wpt\loop`), because the default path hits the linker's length limit for some builds. Never push, tag or merge; the user does that.

## Global Constraints

- `machine/sim.rs`, `proof/gate.rs` and `tatic-kernel` are not edited. `out_stack` keeps its `Vec<K>` type for this reason. If a step seems to need an edit there, stop and report.
- Any test or build over about a minute goes through `run.ps1 -Affinity CFF` (memory-capped). Timed numbers come only from `-Timed` runs.
- Before each commit that touches what they check, these pass: `bash scripts/check/{size_check,test_placement_check,tour_check,cite_check,layout_check,front_matter_check,stack_literal_check,script_header_check,doc_index_check}.sh`.
- `machine.rs` is 765 lines and the spike adds about 75 lines of code, so it stays under the 1000-line limit. Its inline test block is 168 lines, so new machine tests go in a new file, `crates/tatic-wasm/src/machine/loop_tests.rs` (`#[cfg(test)] mod loop_tests;`), which keeps the inline block and the file well under both limits. Run `size_check` and `test_placement_check` anyway.
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
5. An arm that ends in `Br` beside an arm that leaves one word, inside an `If` that is itself an arm. Expected: shape `[W]` for the outer `If`. Test: T2 Step 1.

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
- Modify: `crates/tatic/src/proof/tests/gate_mutants.rs`: make `check` and `row` `pub(super)`.
- Test: `crates/tatic/src/proof/tests/loop_form.rs` (new; register `mod loop_form;` in `proof/tests.rs`); `crates/tatic-wasm/src/machine/loop_tests.rs` (new).

**Interfaces:**
- Produces:
  - `Class::Set`.
  - `impl Class { pub fn pops(self) -> usize; pub fn push(self) -> Option<K>; pub fn takes_operand(self) -> bool }`. `Set` pops 1, pushes `None` and takes an operand, as `Const` does.
  - Row `local.set`, whose operand is the slot; it prints `local.set $p{i}`.
  - `Machine::setter(&self, c: &mut Cx, i: usize) -> Expr` (spike: `setter`, `put`).

- [ ] **Step 0.** Set this plan's and the spec's front matter to `status: active` (commit with Step 4).
- [ ] **Step 1: Failing tests.**
  - `machine/loop_tests.rs` (`#[cfg(test)] mod loop_tests;` in `machine.rs`; make the inline tests' `konst` and `row` helpers, lines 642 to 646, `pub(super)` and import them): `local_set_writes_one_slot`, in the style of `local_get_reads_the_frame`. Over a width-3 frame, for each `i` and `j`, `[get k.., Set i, get j]` reads the new word when `i == j` and the old slot otherwise. The frame's terminal word is untouched.
  - In `loop_form.rs` (with its own copies of `gate_mutants.rs`'s private `SUM` and `src`):
    - `a_no_op_set_prelude_is_accepted`: SUM's accepted `Call` list with `[get 0, Set 0]` prepended gates `Accepted`. Call `gate(..)` directly with `with_entry` and `assert_eq!(.., Verdict::Accepted)`; `check` asserts a rejection.
    - The two rejection tests below use `gate_mutants.rs`'s `check(..)`.
    - `a_set_beyond_the_arity_is_rejected_by_shape`: `[get 0, Set 2, ..]` on an arity-2 entry gives `Rejected(Shape, ..)`, with a message that `contains` `local.set 2`. Messages carry a `position {pos}: ` prefix.
    - `a_set_to_the_padding_slot_is_rejected_by_shape`: `[konst 0, Set 1]` prepended to the accepted list of `tail_pap` (the spike's label for `samples.rs#tail_recursive_loop_with_pap_producing_root_self_call_arg`) (arity 1 in a width-2 frame) gives `Rejected(Shape, ..)`. The spike's d3, which needs `Br`, is ported in T2.
  - Run them. Expected: `local_set_writes_one_slot` fails to compile (it names `Class::Set`); the `loop_form.rs` tests compile (they name the row by string) and fail at run time.
- [ ] **Step 2: Implement.**
  - Add the class, the row and the setter, using the spike's hunks for `setter_ty`, `put`, `setter` and `local_set_row`.
  - `seq_step` pushes `row.class.push()` when it is `Some`.
  - `shape`'s operand rule reads `takes_operand()`.
  - `gets` matches `Ins::Row { name: "local.get" | "local.set", operand }` with the existing bound, and its message becomes `"{name} {operand} is out of the {arity} parameters"`.
- [ ] **Step 3: Verify.** Run the four tests, then `cargo test -p tatic-wasm` and `cargo test -p tatic op_table`. Expected: pass.
- [ ] **Step 4: Commit.** `tatic-wasm: a Set class and the local.set row (params only); kind() becomes push()`.

### Task 2: `Br`, the restart field, and `shape`'s `None`

**Files:**
- Modify: `crates/tatic-wasm/src/machine.rs`:
  - `Ins::Br`, `Ctor::Br`, `MeaningEnv.restart`;
  - `interp(.., calls, restart)` and `meaning`, which thread the field;
  - `ctor_list` (to `[Ctor; 7]`) and `built`;
  - `shape` returns `Option`; `shape_check` compares with `Some(vec![K::W])`; `out_stack` maps `None` to `vec![]`;
  - `well_formed` and its doc; `seq_step`;
  - the docs that say a body returns one word: `shape_check` (lines 122 to 125), `out_stack` (line 199), `well_formed` (lines 203 to 205), and the module doc's constructor list;
  - a one-line comment at `prog` (line 372): it types `nil` from `out_stack`, which is safe only because `check_code` (`sim.rs`) rejects a body whose `out_stack` is not `[W]` first;
  - the `MeaningEnv` literal in the test at line 707. Port the spike's `restart` built from the law's `kk`: `R` is abstract there, so no closed term fits.
- Modify: `crates/tatic-wasm/src/machine/statement.rs` (`G::bm` fills `restart`).
- Modify: `crates/tatic-wasm/src/print.rs`, so its exhaustive match compiles: `Br` prints `br $top`. The wrapper comes in T3.
- Test: `crates/tatic/src/proof/tests/loop_form.rs`; `crates/tatic/src/proof/tests/modules.rs` (the callee cases, which need its private `with_record`); `crates/tatic-wasm/src/machine/loop_tests.rs`.

**Interfaces:**
- Consumes: T1's `Class::Set`, `local.set`.
- Produces:
  - `Ins::Br`.
  - `MeaningEnv { r, ch, calls, restart: At }`, with `restart : Fr -> Mem -> R`.
  - The private `fn shape(..) -> Result<Option<Vec<K>>, String>`.
  - `pub fn out_stack(..) -> Vec<K>`: type unchanged; `vec![]` when every path ends in `Br`.

- [ ] **Step 1: Failing tests.**
  - `machine/loop_tests.rs`: `br_restarts_on_the_current_frame`. With a stub `restart`, `[konst 1, Set 0, konst 9, Br]` reduces to `restart fr' mu`, where `fr'` has slot 0 equal to 1 and the 9 is dropped.
  - `loop_form.rs`, the ported spike tests:
    - Add `pub(super) fn call_form(code: &[Ins], own: usize, arity: usize) -> Vec<Ins>`. It maps each tail `[Set(arity-1) .. Set(0), Br]` back to `Call(own)`. `run()` and every target and mutant start from its output, before any transform. Before T4 it is the identity; after T4 it undoes the pass, so the tests still start from the `Call` form. Self-check: for every target, and for `modules.rs`'s callee `g`, with `c = call_form(compiled list)`, `call_form(restyle(c, own, rev_slots(arity), true), own, arity) == c`. The 100 000-iteration test and `run()` use the same `c`.
    - Port the spike's `restyle` and `setbr_targets_are_accepted`. The 6 targets are the spike's 5 (`capturing_closure_loop` specialised, SUM, SUM2, `partial_application_loop`, `tail_pap`) and `held_out_b` (`test_corpus.rs`), an Accepted tail loop the spike did not cover.
    - Port `setbr_mutants_are_rejected`, 54 mutants, from `setbr_spike.rs` in the spike patch (patch lines 660 to 1048), d3 included, with the spike helpers it needs: `rev_slots`, `replace_nth_call`, `strip_call` and `with_code` (`clip` is already `pub(super)` in `gate_mutants.rs`: import it). Port the mutants only (`setbr_mutants_are_rejected`, patch line 781 on), not `setbr_wat_matches_h4`, `setbr_gate_time` or `setbr_equal_variants_info`. Re-derive each mutant's layer against main's arm rule, and list every layer that differs from the spike's in the report.
  - `a_printed_set_br_loop_runs_100_000_iterations` in `loop_form.rs`:
    - Take SUM's compiled entry, `restyle` it with slots `[1, 0]`, and print it with `print_func`.
    - Wrap it in `(module .. (export "f" (func $f)))`, instantiate it under wasmtime (copy the spike's `verify_setbr_wat_runs_under_wasmtime`; `tail_rule_tests.rs`'s `instantiate` is private) and assert `(100_000, 0)` returns `5_000_050_000`.
    - SUM's compiled list puts the base case in the then-arm (`p0 <= 0`), so `restyle` keeps the arms the right way round.
    - This test needs T3's wrapper: add it in T2 marked `#[ignore = "needs T3's loop wrapper"]`, and remove the ignore in T3.
  - `modules.rs`, the callee cases, on its `rec g` term (`\n. (rec g n acc = ..) n 0`, callee `g` at position 0, arity 2). The helper applies `loop_form::call_form` to `g`'s record first:
    - that record with its tail `Call(0)` replaced by `[Set 1, Set 0, Br]` is `Accepted`;
    - three mutants are rejected: `Br` off the tail, `Set 2` (past the arity), and forward-order `Set`s.
  - `machine/loop_tests.rs`, Review Focus 5: `[.., lt, If([.., lt, If([.., Br], [konst 1])], [konst 2])]` has shape `[W]`.
  - `machine/loop_tests.rs`, `shape` cases:
    - both arms `None`, then `konst 1`: error;
    - both arms `None` as the last instruction of an outer arm: the outer arm is `None`;
    - `[Br, konst 1]`: error;
    - `[konst 1, Br]`: accepted (`None`);
    - `[konst 0, konst 1, lt, If([konst 5, Set 0, konst 1], [Br]), get 0, add]`, arity 1: shape `[W]`;
    - `shape_check` on a body that is all `None`: rejected.
  - `machine/loop_tests.rs`, `a_frame_write_flows_across_the_join`: the last list above, with `p0 = 2`, means the word 6 (the condition is true, and the then-arm's write is what `get 0` reads after the join).
  - Run them. Expected: they fail to compile (no `Ins::Br`).
- [ ] **Step 2: Implement** per the spec's "Details", using the spike's hunks for `Ctor::Br`, `restart`, `interp`'s `br` and `G::bm`.
  - `shape`: `Br` must be last in its sequence, with any stack under it.
  - An `If` arm, from an empty stack, ends on `Some([W])` or `None`. Both `None` gives `None`. Code after `None` is an error.
- [ ] **Step 3: Verify.**
  - Run the `loop_form`, `modules` and `machine` tests. Expected: targets and the callee are `Accepted`; every mutant is rejected at its re-derived layer; Review Focus 5 is `[W]`.
  - Run the workspace suite through the wrapper. Expected: 0 failed.
  - Run `size_check`.
- [ ] **Step 4: Commit.** `tatic-wasm: Br restarts the function on the current frame with the activation's continuation`.

### Task 3: The printer's loop and the shared tail traversal

**Files:**
- Modify: `crates/tatic-wasm/src/print.rs`: `tail_at`, `map_tail_calls`, the loop wrapper in `print_func`, and the docs at lines 12 and 31.
- Test: `crates/tatic/src/jit/tail_rule_tests.rs`; `crates/tatic/src/proof/tests/loop_form.rs` (remove the T2 ignore).

**Interfaces:**
- Consumes: T2's `Ins::Br`.
- Produces:
  - `pub fn map_tail_calls(code: &[Ins], tail: bool, f: &mut dyn FnMut(usize) -> Option<Vec<Ins>>) -> Vec<Ins>`. It replaces each tail-position `Call(j)` with `f(j)` when that returns `Some`, and recurses into both arms of a tail `If`.
  - `fn tail_at(tail: bool, i: usize, len: usize) -> bool`, which both `map_tail_calls` and `print_body` use.

- [ ] **Step 1: Failing test.** In `tail_rule_tests.rs`, `the_tail_rule_has_one_definition`. For each body in `bodies()`:
  - print `map_tail_calls(body, true, &mut |_| Some(vec![Ins::Raw("TAIL".into())]))`;
  - compare it with the plain print, with each `return_call $c0` replaced by `TAIL`. The label is `$c0` because these tests print with `entry_pos = usize::MAX`;
  - assert the texts are equal.
  - Run it. Expected: it fails to compile (no `map_tail_calls`).
- [ ] **Step 2: Implement.**
  - `print_body` computes `last_tail` with `tail_at`.
  - `print_func` wraps the body in `loop $top (result i64)` / `end` (body at depth 6) when the body holds a `Br`.
- [ ] **Step 3: Verify.** Run `cargo test -p tatic-wasm print`, the tie test and the un-ignored 100 000-iteration test. Expected: pass. The goldens are unchanged, since no lowered list holds `Br` yet.
- [ ] **Step 4: Commit.** `tatic-wasm: the printer's loop wrapper and one tail traversal`.

### Task 4: The loop-form pass

**Files:**
- Modify: `crates/tatic/src/jit/lower_wat.rs`: add `pub(crate) fn loop_form`, call it at the end of `Lowering::function`, and update the module doc at lines 8 to 12.
- Modify these tests:
  - `crates/tatic/src/jit/tests.rs`: `a_tail_loop_of_a_million_iterations_installs_and_runs`, lines 783 to 794.
  - `crates/tatic/src/jit/tail_rule_tests.rs`: `tail_rule_prints_both_forms_in_one_body`, lines 142 to 143.
  - `crates/tatic/src/proof/tests/modules.rs`:
    - `a_callee_tail_loop_runs_a_million_iterations`, lines 70 to 79;
    - `call_site_mutants_are_rejected`, its counts and its "sites are 1, 2 and 2" comment.
  - `crates/tatic/src/proof/tests/gate_mutants.rs`: `self_call_site_mutants_are_rejected` and `no_loop_spike_controls_are_rejected`.
  - The goldens under `crates/tatic/tests/golden/`.
- Modify: `PARKED.md`. Add "Dead env pushes before a loop-form `br`" in this commit, since the stopgap is created here. Trigger: a profile showing the pushes.
- Modify: `docs/TOUR.md`, the tail-rule sentence near line 89 (a tail self-call now lowers to the loop form), in this commit: the data flow changes here.

**Interfaces:**
- Consumes: T3's `map_tail_calls`; T1's `local.set`; T2's `Ins::Br`.
- Produces: `pub(crate) fn loop_form(code: &[Ins], own: usize, arity: usize) -> Vec<Ins>`. It is `map_tail_calls(code, true, ..)`, mapping `Call(own)` to `(0..arity).rev().map(Set)` followed by `Br`, and leaving other calls alone.

- [ ] **Step 1: Failing tests and the updated assertions.**
  - `loop_form_rewrites_only_tail_self_calls`, a unit test in `lower_wat.rs`:
    - On `[.., If([konst 0], [.., Call(0)])]` at position 0 with arity 2, the `Call(0)` becomes `[Set 1, Set 0, Br]`.
    - Review Focus 1: `[konst 1, .., If([konst 0], [.., Call(0)]), row add]` is unchanged.
    - A tail `Call(1)` is unchanged.
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
- [ ] **Step 2: Implement** `loop_form`, and call it at the end of `Lowering::function` for every function (spec B1).
- [ ] **Step 3: Re-derive the call-site mutant tests.** After the pass these terms' tail self-call sites are `Set`s and `Br`, so `Call`-site mutators no longer find them:
  - `capturing_closure_loop` and the sum loop, in `gate_mutants.rs`;
  - `tail_recursive_loop_with_pap_producing_root_self_call_arg`, the "pap loop", in `modules.rs`.

  Their loop-form mutants in `loop_form.rs` (T2) cover those sites. For two-argument sites, the `Set`-order and `Set`-slot mutants replace the "two arguments swapped" mutant.

  Expected changes (report each count and layer before and after; a different count is a finding):
  - `gate_mutants.rs`, `self_call_site_mutants_are_rejected`: drop `capturing_closure_loop` from `terms` (it has no `Call` site left), make the array `[(..); 2]`, and delete the "two arguments swapped" assertion (its counter would read 0, not panic: `entry(..).or_default()`) and the now-dead `arity == 2` branch in "the Call dropped". The other counts go from 4 to 3. Every remaining term has arity 1, so the `if *arity == 1 { Shape } else { Walk }` pick and its "on two parameters" comment go too.
  - `gate_mutants.rs`, `no_loop_spike_controls_are_rejected`: the call-site asserts (`at_each_site(..) >= 1`) are skipped for the sum loop only (guard them on `count_call_sites(&code, 0) > 0`) and kept for factorial and fib, which are unchanged; their `arity == 2` layer picks become dead and go. The sum loop's other controls (operator swaps, branches swapped, the condition's `local.get`, the base case) now run on the loop form; re-derive their layers from the first run. Update the doc comment at lines 245 to 247.
  - `modules.rs`, `call_site_mutants_are_rejected`: the swap site is the pap loop's two-argument call into the callee, which stays, so "swapped" stays 1 and the `arity >= 2` branch stays live. The other counts go from 5 to 4, and the comment reads "sites are 1, 2 and 1".
  - Its layers change: in the pap loop that site is now followed by `[Set 0, Br]`, not `Call(own)`, and `Br` drops a surplus word, so an added argument instruction passes `shape`, and a wrong callee may. Expected: added `Walk` (the extra word shifts the arguments the callee pops, and the one left over is dropped by `Br`, so `shape` passes); wrong callee `Pairing` where the substitute's arity is at most the words pushed, otherwise `Shape`; dropped stays `Shape` (the arguments underflow). Replace the single `if kind == "two arguments swapped" { Walk } else { Shape }` with a per-term, per-kind layer taken from the first run, and report each.
  - Remove imports left unused (for example `EvalError`), so the build has no new warnings.
- [ ] **Step 4: Goldens and verdicts.**
  - Run `UPDATE_GOLDEN=1 cargo test -p tatic --test golden_wat`, then `git diff --stat crates/tatic/tests/golden/` and the full diff.
  - Expected: only self-tail-recursive functions change. Each gains the wrapper lines, has its body re-indented by two, and has its tail call's lines replaced. Non-self `return_call`s stay (`twice_inc_5`, the `a_pap_*` terms, `a_capturing_closure_call`).
  - Expected: 11 goldens change (`capturing_closure_loop` and its `_specialised`, `closure_typed_loop_carried_parameter_loop`, gcd, `gcd_with_two_base_cases`, `inconsistent_arity_loop_carried_parameter_loop`, iterate, `partial_application_loop` and its `_specialised`, and the two `tail_recursive_loop_*` terms). Report the list; any other change is a finding.
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
  - the new guards: the definitional tests, `loop_form.rs` and the tail-rule tie test.
- Modify: `docs/TOUR.md`: `Set`, `Br`, the loop form and the loop-form pass in the glossary (the line-89 sentence changed in T4).
- Modify: `PARKED.md`:
  - "LocalSet and scratch locals": params-only `Set` is built;
  - "Learned target-cost model": its status line from 1342f07 becomes "parked; Set and Br adopted";
  - the invalid-wasm and h4 lines, if any remain;
  - if the spec's O3 was not adopted, a parked entry for it (trigger: a change to `shape`, or a cold-time budget that O3's smaller rule set would help).
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

The spec's table is the reference. In summary:
- `Class` gains `Set`, and `kind` becomes `push` (T1).
- `Br` and the restart field are added (T2).
- `print_body`'s tail logic becomes one traversal that the pass shares (T3).
- `lower_wat.rs` gains `loop_form` (T4).
- Removed:
  - `Class::kind`;
  - `return_call $f` for self-calls in printed text;
  - the `call`-traps control;
  - the stale "stands for `return_call`" comments.
- The tail rule stays for calls to other functions.
- New stopgap: the dead env pushes, parked in T4's commit.
