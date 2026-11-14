---
status: done
---

# Closures through the gate Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** the 8 in-scope census rows go from `NotCovered` to `Accepted`. The gate reads closed closure values and closure calls as words, and the machine models the closure word's rows and `call_indirect` through the table.

**Architecture:**
- New rows replace the lowering's `Raw` lines: `shl`, `shr_u` and `or` (Word); `wrap` and `extend` (a new `Unary` class); `i32.const` (Const).
- `Ins::CallIndirect(a)` is a new instruction. Its machine meaning is a `choose` chain over the module's dynamic set for arity `a`, and each arm is the existing static call.
- The source reading gains `Src::Apply`, a closure call that uses the same chain built by the same helper.
- A closed lambda reads as its packing, built from the same rows, so the walk meets the same guarded sites.
- One dynamic set, held by `Ctxt`, serves both sides.

**Tech Stack:** Rust workspace (`tatic`, `tatic-wasm`, `tatic-kernel`); Church bit-vector circuits; wasmtime for the golden and op-table legs.

**Spec:** `docs/superpowers/specs/2026-11-13-closures-through-the-gate-design.md` (decisions r1 s1 t1 u1, 2026-11-13).

The spec was corrected inline for three things recon found: D1's `choose` chain, D2's unguarded Unary sites with no `PrimOp`, and D7's precheck. "Calls this plan made" (at the end) lists what the plan settled.

The user picked, on 2026-11-13: general rows (x1), refuse direct calls into Pointer records (y1), the T0 split into `machine/prog.rs` (z1), the dynamic sets held on `Ctxt` and passed down (a1), subagent-driven execution with T0 first (b1, c1).

## Global Constraints

- The 34 golden WAT files (`crates/tatic/tests/golden/*.wat`) stay byte for byte. Check with `cargo test -p tatic --test golden_wat`; never use `UPDATE_GOLDEN=1`.
- No other row of `proof/tests/baseline.rs#VERDICTS` moves. `BASELINE` (installs, compiled, specialised, tree) does not change.
- No census row gets a `Rejected` verdict or panics (`verdicts_match`).
- The source reading never reads the `Ins` list. The dynamic set comes from the records' `arity` and `env` only.
- Printed lines, exactly:
  - `i64.shl`, `i64.shr_u`, `i64.or`
  - `i32.wrap_i64`, `i64.extend_i32_u`
  - `i32.const {k}`, `i64.const {k}`
  - `call_indirect (type $ty{a})`, never `return_call_indirect`
- Row semantics at width `n` (a power of two):
  - Shift rows shift by the amount's low `log2 n` bits (wasm's `i64.shl` at n = 64).
  - `wrap` keeps the low `min(32, n)` bits.
  - `extend` is the identity: an `i32` is a zero-extended word (D3).
- `cargo test` takes one name filter. Several names go after `--`: `cargo test -p tatic --lib -- a b`.
- Any thread that builds a statement or proof uses `CHECK_STACK`. Never write a stack size as a number (`stack_literal_check.sh`).
- Any `cargo test` expected to run over about a minute goes through `~/.claude/runs/run.ps1 -Affinity CFF` with `-j 10`. Never let python read stdin.
- Before each commit, run the repo guards that cover what it touches: `bash scripts/check/<name>` for `size_check.sh`, `test_placement_check.sh`, `tour_check.sh`, `cite_check.sh`, `layout_check.sh`, `stack_literal_check.sh` and `doc_index_check.sh`.

## Review Focus

1. **A closure call whose index is outside the dynamic set.** The index may name a table slot of another arity, a direct-only record, or the entry's own position, or it may be past the table. Both sides must answer `z`, and a raw index must never reach `Ctxt::table`'s own-first chain. Pinned by T2's `a_dynamic_call_outside_the_set_answers_z` and `a_dynamic_call_of_another_arity_answers_z`, which assert both `hc` and `sc`.
2. **A module that reads a closure and has a table slot the model does not see.** The slot may be a pap wrapper `Item::Text` or a curried stage, or the module may be curried with no bare value. The verdict must be `NotCovered`, never `Accepted` and never `Rejected(Shape)`. Pinned by T4's `a_closure_call_beside_a_pap_slot_is_not_covered` and `a_curried_closure_call_is_not_covered`.
3. **A source closure call with no matching `CallIndirect` in the code, or the reverse.** On a non-empty set the verdict must be `Rejected(Pairing)` (the widened callee sets differ), never a panic in `SEnv::callee`'s lookup; on an empty set the walk rejects it. Pinned by T4's `a_dropped_closure_call_is_rejected_by_pairing` and by T5's mutant on a row with a non-empty set.
4. **A closure body that reaches its caller through the table.** The verdict must be `NotCovered`, not a panic in `Ctxt::real`. Pinned by T2's `a_dynamic_cycle_is_found` and T4's `a_closure_cycle_is_not_covered`.
5. **Width n = 8, where every machine and sim test runs.** At this width a shift by 32 is a shift by 0 and `wrap` is the identity. So tests of the halves' values run at n = 64 (T1's `closure_word_rows_agree_with_u64_at_n64`), and the T2 controls assert answers, not halves.

---

### Task 0: Split the program meanings out of `machine.rs`

`crates/tatic-wasm/src/machine.rs` is 896 lines and has two responsibilities: the instruction set with its shape check, and the `Prog` constructors with their meanings. T1 and T2 add about 150 lines, which would take it past the 1000-line limit. Split it first, mechanically, as its own commit.

**Files:**
- Create: `crates/tatic-wasm/src/machine/prog.rs`.
- Modify: `crates/tatic-wasm/src/machine.rs`. Move lines 258-714 into `prog.rs`: `prod`, `mkpair`, `nat2`, `nat2_lit`, `Ctor`, `ctor_list`, `ctor_idx`, `Machine`, `MeaningEnv`, `F_TY` and `impl Machine`. Then add `mod prog; pub use prog::*;`.
- Modify: `docs/TOUR.md`. The `machine.rs` bullet names `machine/prog.rs` for the constructors and their meanings.

**Interfaces:**
- Produces: no public path changes.
- Private methods used outside the moved range become `pub(super)`. These include `Machine::split` (used in statement.rs) and `Machine::word` (used in the machine.rs tests). Let the compiler find any others, and list them all in the commit message.

- [ ] **Step 1:** Record the pass count of `cargo test -j 10 -p tatic-wasm --lib`.
- [ ] **Step 2:** Move the items. Change only their visibility, never their bodies.
- [ ] **Step 3:** Run `cargo test -j 10 -p tatic-wasm --lib`. Expected: the same pass count as Step 1.
- [ ] **Step 4:** Run `bash scripts/check/size_check.sh && bash scripts/check/tour_check.sh`. Expected: ok.
- [ ] **Step 5: Commit.** `git add crates/tatic-wasm/src/machine.rs crates/tatic-wasm/src/machine/prog.rs docs/TOUR.md && git commit -m "refactor: the Prog constructors' meanings move to machine/prog.rs"`

### Task 1: The closure word's rows and the `Unary` class

**Files:**
- Modify: `crates/tatic-wasm/src/encoding/gates.rs`. Add the circuits `shl(n)`, `shr_u(n)`, `wrap(n)` and `extend(n)`, and a one-operand `bits_circuit1` beside `bits_circuit`. `or` reuses `proofs.rs#or_bv`.
- Modify: `crates/tatic-wasm/src/machine.rs`. Add `Class::Unary`: `pops` is 1, `push` is `Some(K::W)`, `takes_operand` is false.
- Modify: `crates/tatic-wasm/src/machine/prog.rs`.
  - Add `Ctor::Leaf(Class::Unary)` to `ctor_list`, which becomes `[Ctor; 8]`.
  - Its `ctor_ty` is `(V -> V) -> F(V,A) -> F(V,A)`.
  - Its meaning pops `x` and continues with `op x` pushed. It takes no domain argument and has no guard.
  - Add its `seq_step` arm.
- Modify: `crates/tatic-wasm/src/ops.rs`. Add `unary_row!` beside `circuit_row!`, and `i32_const_row()` beside `const_row()`.
- Modify: `crates/tatic-wasm/src/wasm.rs`.
  - In `table()`, append after `lt_u`: `shl`, `shr_u` and `or` (Word, `Dom::TOTAL`); `wrap` and `extend` (Unary); `i32.const` (Const).
  - In the test, update the names list, the case array (`[(&str, i64); 12]` becomes `18`) and the `want` match.
- Modify: `crates/tatic/src/jit/op_table_tests.rs`, `crates/tatic/src/proof/tests/gate_mutants.rs`.
- Test: `crates/tatic-wasm/src/machine/sim/tests.rs`.

**Interfaces:**
- Produces: the row names `"shl"`, `"shr_u"`, `"or"`, `"wrap"`, `"extend"` and `"i32.const"` in `wasm::table()`.
- Produces: `Class::Unary`.
- Produces, in `encoding::gates`:
  - `pub fn shl(n: usize) -> Expr` and `pub fn shr_u(n: usize) -> Expr`, of type `V -> V -> V`;
  - `pub fn wrap(n: usize) -> Expr` and `pub fn extend(n: usize) -> Expr`, of type `V -> V`.

- [ ] **Step 1: Write the failing tests.**
  - `wasm.rs#wasm_rows_are_closed_and_typed`:
    - The names list becomes these 17 names, in table order: `const, local.get, local.set, add, sub, mul, mod, lt, le, eq, lt_u, shl, shr_u, or, wrap, extend, i32.const`.
    - Add the cases `("shl",0), ("shr_u",0), ("or",0), ("wrap",0), ("extend",0), ("i32.const",7)`.
    - Add `Class::Unary => arrow(V, V)` to `want`.
  - `op_table_tests.rs#closure_word_rows_agree_with_u64_at_n64`. Take the edge set `[0, 1, 31, 32, 63, 64, 100, 2^31-1, 2^32, u64::MAX]`.
    - Over its pairs, `def_eq(app2(row "shl", lit a, lit b), lit(a.wrapping_shl(b as u32 % 64)))`. Likewise `shr_u` (with `wrapping_shr`) and `or` (with `a | b`).
    - For each `a`, `def_eq(app(row "wrap", lit a), lit(a & 0xffff_ffff))`.
    - For each `a < 2^32`, `def_eq(app(row "extend", lit a), lit a)`.
    - The `i32.const` row pushes `lit 7` at operand 7 and `lit 0xffff_ffff` at operand `-1`.
    - Pair each assertion with one non-`def_eq` assertion against the expected value + 1.
  - `machine/sim/tests.rs#a_unary_site_adds_no_branch` (w2). Take an arity-1 entry with code `[get 0, Row("extend"), Row("wrap")]`.
    - It is proved against a source that answers `k(wrap(extend(x)))` with no `choose`.
    - It is refused against the same source wrapped in `choose(.., .., z)`, with `"body: the machine returns but the source branches"`. Check the exact text against `sim.rs#sim_step`'s fallback before asserting it.
- [ ] **Step 2:** Run `cargo test -j 10 -p tatic-wasm --lib -- wasm_rows_are_closed_and_typed a_unary_site_adds_no_branch` and `cargo test -j 10 -p tatic --lib closure_word_rows_agree_with_u64_at_n64`. Expected: compile errors, since `Class::Unary` and the rows don't exist yet.
- [ ] **Step 3: Implement.**
  - The shifters are the probe's barrel shifter (`fn shift` in `docs/runs/2026-11-13/patches/q2-literal-probe.patch`), generalised to `log2 n` stages.
  - `seq_step` keeps its domain argument for Word rows only (`row.class == Class::Word`).
- [ ] **Step 4: Update `gate_mutants.rs#every_row_has_an_operator_swap_mutant`.**
  - Iterate only over rows that `carrier()` can build, meaning rows with a `PrimOp`.
  - Assert that `shl`, `shr_u` and `or` are among the rows `carrier()` cannot build, and that no row it built before is now skipped.
  - Pin `next()` to the successor among carried rows, so `mod`'s swap target stays the same. Record the swap pairs before and after in the commit message.
  - `op_table_tests.rs#agree` keeps iterating over `PrimOp::ALL`.
- [ ] **Step 5:** Re-run Step 2's commands, then `cargo test -j 10 -p tatic-wasm --lib` and `cargo test -j 10 -p tatic --lib -- op_table every_row_has_an_operator_swap_mutant`. Expected: PASS.
- [ ] **Step 6: Commit** the files above: `git commit -m "feat: the closure word's rows and the Unary class"`.

### Task 2: `call_indirect` in the machine and the statement

**Files:**
- Modify: `crates/tatic-wasm/src/machine.rs`.
  - Add `Ins::CallIndirect(usize)` and its `shape` arm.
  - `shape_check` admits `EnvAccess::Pointer` and refuses `Params(k)` with `k > 0`.
  - `shape_check` also refuses an `Ins::Call(j)` whose callee `j` is `Pointer`, with "a direct call into a record reached through an environment pointer" (decision y1).
  - Add `pub fn dynamic_set`, `pub fn dynamic_sets`, `pub fn callees` (moved here from `statement.rs`) and `pub fn dispatch_chain`.
- Modify: `crates/tatic-wasm/src/machine/prog.rs`.
  - Add `Ctor::CallIndirect` to `ctor_list`, which becomes `[Ctor; 9]`. Add its `ctor_ty`, its cons, its meaning and its `seq_step` arm.
  - `MeaningEnv` becomes `MeaningEnv<'a>` and gains `dynamic: &'a [Vec<usize>]`, which keeps it `Copy`.
  - Update `MeaningEnv`'s 3 constructors: in the machine.rs tests, in `loop_tests.rs:20`, and in `statement.rs` `G::bm`. `G::bm` and `G::bs` gain a `dynamic: &[Vec<usize>]` parameter.
- Modify: `crates/tatic-wasm/src/machine/statement.rs`.
  - `Ctxt` gains `dynamic: Vec<Vec<usize>>`, built once in `Ctxt::new` by `dynamic_sets` over the module's `.entry`s.
  - `widen` takes the frame width over every record's arity and every `CallIndirect(a)`'s `a` in any record's code (recursing into `If`), so a closure call wider than every record (`\f. f 1 2` against arity-1 records) builds its callee frame without tripping `frame`'s assert.
  - `SEnv` becomes `SEnv<'a>` and gains `dynamic: &'a [Vec<usize>]`.
  - Extract `SEnv::callee(&self, pos) -> At` (`own` gives `g`, otherwise the `callees` lookup) from `SEnv::call`, which keeps its behaviour by calling it.
  - Add `SEnv::call_dyn` and `pub fn call_cycle`.
  - `bm_bs` uses the widened `callees`.
- Modify: `crates/tatic-wasm/src/machine/sim.rs`.
  - `proof_open` runs before any `Ctxt` exists, so it computes `dynamic_sets` over the module's `.entry`s itself and uses the widened `callees`.
  - `closed` drops its `path` parameter: `call_cycle` replaces that check for static and dynamic edges alike, and has run before `closed` is reached. It keeps one `debug_assert`.
- Modify: `crates/tatic-wasm/src/print.rs`. Add the `print_body` arm.
- Test:
  - `crates/tatic-wasm/src/machine/sim/tests.rs`. Its mirror `Src` gains `Apply(Box<Src>, Vec<Src>)`.
  - The `print.rs` tests.
  - `crates/tatic/src/proof/tests/gate.rs`.

**Interfaces:**
- Consumes: T1's rows `"wrap"` and `"eq"`, through `row_term`.
- Produces `Ins::CallIndirect(usize)`, where the field is the arity `a`.
  - It pops the index word, then `a` argument words, then the environment word, and pushes one word.
  - It prints as `call_indirect (type $ty{a})`.
- Produces `pub fn dynamic_set(records: &[Option<&Entry>], arity: usize) -> Vec<usize>`.
  - It returns, in ascending order, the positions `p` with `records[p] = Some(e)`, `e.env == EnvAccess::Pointer` and `e.arity == arity`.
  - This is the only place the set is defined.
- Produces `pub fn dynamic_sets(records: &[Option<&Entry>]) -> Vec<Vec<usize>>`: `dynamic_set` for every arity up to the largest record arity, indexed by arity. It takes bare entries, not `ModEntry`s, because the gate's `build` has only `Entry`s before any source exists; `Ctxt::new`, `proof_open` and `closed` map their module with `.entry`. `Ctxt::new`, `proof_open`, `closed`, `call_cycle` and the gate's `pairing` call it; the gate's cost calls `dynamic_set` per arity. No other code builds a set.
- Produces `pub fn callees(k: usize, code: &[Ins], dynamic: &[Vec<usize>]) -> Vec<usize>`.
  - It returns the static `Call` targets plus `dynamic[a]` for every `CallIndirect(a)`, recursing into `If`. The result is deduplicated, ascending, and excludes `k`.
  - An arity `a` past `dynamic.len()` contributes nothing.
- Produces `pub fn dispatch_chain(c: &mut Cx, set: &[usize], z: Expr, step: &mut dyn FnMut(&mut Cx, usize, Expr) -> Expr) -> Expr`.
  - It folds the set from the right: `step(p1, step(p2, .. z))`, where `step(p, rest)` builds one test-and-arm.
  - Both sides call it with the same `set`, so the order cannot drift.
- The dispatch test is `encoding::gates::eq_bit(n)` (gates.rs:175, `V -> V -> Bv_1`), the term the `eq` row's meaning is built from, used directly and never looked up by row name (`Machine::row` panics on a table without `eq`, such as `toy_table.rs`'s, and `interp` builds every constructor's meaning for every program). No new function. Both sides' tests are `eq_bit(n) idx (lit p)`, so the walk's condition check (`def_eq`) sees one term. `eq_bv`, which answers a Church boolean, is not a `choose` condition and must not be used here.
- Produces `impl SEnv { pub fn call_dyn(&self, c: &mut Cx, idx: Expr, args: &[At], k: &dyn Fn(&mut Cx, Expr) -> Expr) -> Expr }`.
  - It binds `kont` once, then calls `dispatch_chain` over `self.dynamic.get(args.len())` (empty if absent).
  - Each step is `self.choose(c, eq_bit(n) idx (lit p), self.callee(p) args.. kont, rest)`.
- Produces `pub fn call_cycle(records: &[Option<&Entry>]) -> Option<usize>`.
  - It returns a position on a cycle of the widened callee graph, with self-edges excluded, or `None`.
- Produces `Ctor::CallIndirect`, one constructor for every arity, shaped like `Call`.
  - `ctor_ty`: `Pi S. (S -> V x (Fr x A)) -> V -> F(V,A) -> F S`. The per-site unpack pops `idx`, then the `a` arguments into the callee frame, then drops the environment word. The `V` operand is `lit(n, a)`, the arity, as `Call`'s operand is `lit(n, j)`.
  - Meaning: an `eq_bv` pick on the arity operand over the module's arities, `(op == a1) chain_a1 ((op == a2) chain_a2 .. z)`, where `chain_a` is `dispatch_chain(env.dynamic[a])` with steps `pick(eq_bit(n) idx (lit p), calls (lit p) fr2 mu kont, rest)`, `pick` being the probe `ch` in the proof and `choose` in the statement as in `interp`, and `kont` bound once.
  - The arity pick is the static table's precedent: at a literal operand it reduces by conversion, so the walk never meets it and sees only `chain_a`'s `ch` heads.

- [ ] **Step 1: Write the failing tests** in `machine/sim/tests.rs`.
  - Add a helper `dyn_module(n, records: Vec<(Entry, Box<SrcFn>)>)` modelled on `two_entries`.
  - The base module has three records:
    - Position 0: `Pointer`, arity 1, body `[get 0, konst 1, Row("add")]`, source `x + 1`.
    - Position 1: `Params(0)`, arity 3, body `[get 0]`, source `Param 0`.
    - Position 2, the entry: `Params(0)`, arity 1, code `[get 0, konst 32, Row("shr_u"), konst 5, get 0, Row("wrap"), CallIndirect(1)]`.
  - `prove_takes_a_dynamic_call`: the mirror source `Apply(Param 0, [Lit 5])` is proved, and `holds(proof, statement)`. In cps it is the guarded `shr_u` site, then the args, then the head again, then `call_dyn(wrap(head), ..)`.
  - `a_dynamic_call_outside_the_set_answers_z`: at fuel `lit 3`, the entry's real `sc` and `hc` are both `def_eq` to `z` at each of these heads:
    - `a = lit 1` (position 1, which is not `Pointer`);
    - `lit 2` (the entry itself);
    - `lit 9` (past the table).
  - `a_dynamic_call_of_another_arity_answers_z`: with position 0 given arity 2, the set for arity 1 is empty, so at fuel `lit 3` `sc` and `hc` at head `lit 0` are `def_eq` to `z`.
  - `a_closure_call_wider_than_every_record_answers_z`: the base module with the entry's `CallIndirect(1)` changed to `CallIndirect(4)` and three more `konst` arguments pushed before the head. The base module's widest record has arity 3, so without the `widen` change this trips `frame`'s assert. Building the statement does not panic, and at fuel `lit 3` `sc` and `hc` at head `lit 0` are `def_eq` to `z` (no record has arity 4, so the arity is past `dynamic.len()`).
  - `a_table_without_eq_still_gates` (in `crates/tatic/src/proof/tests/toy_table.rs`): the toy table, which has no `eq` row, still gives its existing verdicts after `Ctor::CallIndirect` exists.
  - `prove_refuses_a_dynamic_call_against_a_static_one`: a source identical to the one in `prove_takes_a_dynamic_call` except that it dispatches through `call(0, ..)` instead of `call_dyn`. It keeps the `shr_u` site. It is refused by the walk at the dispatch, with a message naming `branches` (the machine's chain) against `calls`.
  - `a_closure_call_with_its_head_evaluated_once_is_rejected` (spec Review Focus 5):
    - The module has a `Params(0)` record at 1 that answers a word, and an entry that evaluates its head through `call $c1` twice, without `Call(0)`.
    - A source that calls `$c1` once and reuses the result is refused by the walk with "the machine calls a function but the source".
  - `a_dynamic_cycle_is_found`:
    - Records 0 and 1 are both `Pointer`, arity 1, each with body `[get 0, konst 32, Row("shr_u"), konst 1, get 0, Row("wrap"), CallIndirect(1)]`. Then `call_cycle` gives `Some(_)`.
    - With record 1's body changed to `[get 0]`, it gives `None`. Record 0 then has only a self-edge and an edge to 1.
  - In the `print.rs` tests: `print_body` of `[CallIndirect(2)]` prints `call_indirect (type $ty2)`, also in tail position.
  - In `proof/tests/gate.rs`:
    - `a_pointer_record_passes_the_shape_check`: a `Pointer` record of arity 1 with body `get 0`.
    - `a_direct_call_into_a_pointer_record_is_refused`: a `Call(0)` into such a record gives `Rejected(Shape)`.
    - `a_record_with_an_env_parameter_is_rejected_by_the_shape_check` (`Params(1)`) stays unchanged.
- [ ] **Step 2:** Run `cargo test -j 10 -p tatic-wasm --lib machine::sim` and `cargo test -j 10 -p tatic-wasm --lib print`. Expected: compile errors.
- [ ] **Step 3: The instruction and the set.**
  - The `shape` arm pops `[W; a + 2]` and pushes `W`.
  - Move `callees` into `machine.rs` with the new parameter, and update its 4 callers:
    - `statement.rs` `bm_bs` (passes `&self.dynamic`);
    - `sim.rs` `proof_open` and `closed` (pass `dynamic_sets` over the module's `.entry`s);
    - `gate.rs` `pairing` (T4 widens it; until then it passes `&[]`).
- [ ] **Step 4: The constructor.** Implement it as given in Interfaces, through `dispatch_chain`.
- [ ] **Step 5: The source side and the cycle check.**
  - Add `SEnv::call_dyn`.
  - Implement `call_cycle` over the widened `callees`.
  - `Ctxt::real` keeps its assert, and the message gains "(call_cycle rules this out before a statement is built)".
- [ ] **Step 6:** Run `cargo test -j 10 -p tatic-wasm --lib`, then `cargo test -j 10 -p tatic --lib proof::tests`. Expected: PASS, with no existing test changing its verdict.
- [ ] **Step 7:** Run `bash scripts/check/size_check.sh && bash scripts/check/test_placement_check.sh`. Expected: ok. `sim/tests.rs` is 334 lines now; if it passes the limit, split it by topic first.
- [ ] **Step 8: Commit** with explicit paths: `git commit -m "feat: call_indirect in the machine, its dispatch over the dynamic set"`.

### Task 3: The lowering emits the rows and `CallIndirect`, with derived type lines

**Files:**
- Modify: `crates/tatic/src/jit/lower_wat.rs`.
  - Change `Node::MakeClosure`, `Node::MakePap`, `Node::CallUnknown` (`Fast`), `push_closure_env`'s empty case and `dynamic_apply`.
  - Delete `call_indirect_arities`.
  - `lower()` derives the `$tyK` lines.
  - The `CompiledFragment` literal (`:311`) gains `curried`.
- Modify: `crates/tatic/src/jit/compile.rs`. Add `CompiledFragment.curried: bool`, set from the registry's dispatch choice (`reg.needs_generic_dispatch`).
- Modify: `crates/tatic/src/proof/tests/toy_table.rs`. Its literal gains `curried: false`.
- Modify: `crates/tatic/src/testing/ins_mutate.rs`, in `arg_ranges`:
  - Add the arm `Ins::CallIndirect(a) => a + 2`.
  - Fix `Ins::Call(j)` to pop callee `j`'s arity rather than the enclosing call's. `arg_ranges` and `edit_call_site` take `arities: &[usize]`, built from the fragment's records; update `edit_call_site`'s two callers (`gate_mutants.rs:165`, `modules.rs:180`).
  - A Unary row already pops 1 through `class.pops()`.

**Interfaces:**
- Consumes: T1's row names and T2's `Ins::CallIndirect(usize)`.
- Produces: `CompiledFragment { .., curried: bool }`.

- [ ] **Step 1: Write the failing test** `jit/compile/tests.rs#closure_lines_are_rows`. Compiling `non_tail_closure_carrying_recursion` gives:
  - no `Ins::Raw` in any record;
  - the rows `i32.const` (operand 0), `extend`, `shl` and `or` in the entry;
  - `shr_u`, `wrap` and `CallIndirect(1)` in `$c0`;
  - `curried == false`.

  Also check:
  - `twice`'s entry holds `CallIndirect(1)`.
  - An `arg_ranges` case (make `arg_ranges` `pub(crate)` in `testing/ins_mutate.rs`): in `tail_recursive_loop_with_if_between_closures_self_call_arg`, the argument ranges of the `CallIndirect` cover the nested `call $c0` whole.
- [ ] **Step 2:** Run `cargo test -j 10 -p tatic --lib closure_lines_are_rows`. Expected: FAIL.
- [ ] **Step 3: Implement.**
  - Replace each closure-word `raw(..)` with its row, using `konst(32)` for `i64.const 32`.
  - Replace the `call_indirect` raw and its side-list push with `w.push(Ins::CallIndirect(args.len()))`, in `Fast` and in `dynamic_apply` alike.
  - Curried modules keep their `Raw` tee and set lines, so they stay unmodelled; their type lines are derived too.
  - `push_closure_env` with no captures pushes the `i32.const` row with operand 0. With captures it stays `Raw`.
  - `lower()` collects the `CallIndirect` arities over every `Item::Func` record's code, recursing into `If`. It sorts and deduplicates them, then prints the same `(type $ty{k} ..)` lines.
- [ ] **Step 4:** Run `cargo test -j 10 -p tatic --test golden_wat` and `cargo test -j 10 -p tatic --lib jit::`. Expected: PASS, and `git status crates/tatic/tests/golden` is clean.
- [ ] **Step 5:** Run `cargo test -j 10 -p tatic --lib -- verdicts_match baseline_fixture_matches`. Expected: PASS with every verdict unchanged. The reading still refuses the 8 rows, so this shows the lowering change moved nothing.
- [ ] **Step 6: Commit** with explicit paths: `git commit -m "feat: the lowering emits the closure word as rows and call_indirect as an instruction"`.

### Task 4: The source reading takes closure values and closure calls

**Files:**
- Modify: `crates/tatic/src/proof/gate.rs`.
  - Add `Src::Apply`, its `parse` arms and its `cps` arm.
  - `Reading` gains `fast: bool`, which `build` sets; `parse` reads a closure only when it is true.
  - `build` gains the `call_cycle` check, between `shape_check` and `pairing`.
  - `pairing` compares widened callee sets, through a new walker `closure_call_arities`.
  - Update `call_sites`, `cost` (gate.rs:200), `module_cost` and `callee_heads`.
- Modify: `crates/tatic/src/proof/tests/baseline.rs`.
  - The 8 rows in `VERDICTS` become `Accepted`.
  - `measure_verdict`'s `raw` drops its `env == Pointer` clause.
- Modify: `crates/tatic/src/proof/tests/gate.rs`. Update `what_cps_cannot_take_is_not_covered` and the two `call_sites` call sites (`:549` and `:596`), and add the new tests.

**Interfaces:**
- Consumes: T2's `call_cycle` and `SEnv::call_dyn`; T3's `curried`.
- Produces: `Src::Apply(Box<Src>, Vec<Src>)` (the head and the arguments). The set comes from `SEnv.dynamic`.
- `source_fn` gains a `fast: bool` parameter, which `build` computes once and passes; `source_fn` stores it in `Reading`.
- Produces: `fn call_sites(store: &TermStore, h: Hash, width: &dyn Fn(usize) -> u64) -> u64`, and `cost(store, h, callees, width)` passing `width` through.
- Produces: `fn closure_call_arities(store: &TermStore, h: Hash) -> Vec<usize>`: for each closure call in `h`'s body, a `VarCall`'s `args.len()` or an over-applied `CombinatorCall`'s `args.len() - m`, deduplicated.

- [ ] **Step 1: Write the failing tests.**
  - In `baseline.rs#VERDICTS`, these 8 rows become `Kind::Accepted`:
    - `twice`
    - `iterate`
    - `iterate_creating_a_closure_over_g`
    - `closure_typed_loop_carried_parameter_loop`
    - `non_tail_closure_carrying_recursion`
    - `branching_non_tail_closure_carrying_recursion`
    - `tail_recursive_loop_with_if_between_closures_self_call_arg`
    - `inconsistent_arity_saturating_instance`
  - In `gate.rs`:
    - `a_closure_call_beside_a_pap_slot_is_not_covered`: take `twice`'s compiled fragment, insert an `Item::Text` at position 0, and shift `entry_pos` and every `Item::Func`'s `pos` (and its source position) by one. The result is `NotCovered`.
    - `a_curried_closure_call_is_not_covered`:
      - `twice`'s fragment with `curried = true` is `NotCovered`.
      - So is every census row whose fragment is curried and reads a closure. Enumerate these from the fixture and assert that none is `Rejected`.
    - `a_closure_cycle_is_not_covered`: `call_cycle` runs before `pairing`.
      - Compile the closed `\x. (\f. f 5) (\y. (\g. g 1) (\z. z + 1))` (a capturing term would be refused earlier, as outside the reading). Its closure `\y. ..` is a `Pointer` record of arity 1 that makes a closure call of arity 1 (through the combinator or inlined), which reaches every arity-1 `Pointer` record, `\y. ..` among them: a cycle by the set's over-approximation.
      - Print the fragment in the test's failure message. Assert `NotCovered` with "cycle".
      - If the fragment has no such cycle (the lowering may shape it otherwise), drop this test, rely on T2's `a_dynamic_cycle_is_found`, and record a ruling.
    - `a_dropped_closure_call_is_rejected_by_pairing`: in `non_tail_closure_carrying_recursion`'s `$c0`, whose set `{1}` is non-empty, replace the tail `get $p1; Row("wrap"); CallIndirect(1)` with `Row("add")`, which takes the environment half and the argument and leaves the stack balanced. The code's callees lose position 1 while the source's keep it, so the result is `Rejected(Pairing)`, not a panic.
    - `a_pointer_record_calling_its_own_arity_pairs`: a module whose `Pointer` record of arity 1 makes a closure call of arity 1 is not `Rejected(Pairing)`. Its own position is in `dynamic_set(1)` on the source side but dropped by `callees` on the code side, so `pairing` must remove the record's own position after the union. Compile `\x. (\f. f (\z. z + 1)) (\y. y 1)`: `\y. y 1` is a closed value, a `Pointer` record of arity 1 whose body makes an arity-1 closure call (print the fragment in the failure message). Without the removal of `p` the result is `Rejected(Pairing)`.
    - `a_closure_call_costs_its_width_and_its_head_twice`:
      - `call_sites` of `\f. f 1` is `3` with `width = |_| 3`, and `1` with `|_| 0`, because of the `max(1, ..)`.
      - For the entry term of `tail_recursive_loop_with_if_between_closures_self_call_arg`, quote the term in a comment and work out by hand `2 * (1 + Σ head-arg sites) + max(1, w) + Σ extra-arg sites` at `w = 1`. Assert that integer.
  - `what_cps_cannot_take_is_not_covered`:
    - Remove `twice` and `\f. f 1`, which are now taken.
    - Add a capturing closure (`\x. (\y. x + y)`) and a partial application, both still `NotCovered`.
- [ ] **Step 2:** Run `cargo test -j 10 -p tatic --lib proof::tests`. Expected: FAIL.
- [ ] **Step 3: `parse`.**
  - Every closure arm below applies only when `reading.fast` holds and the table has the rows it uses (`shl`, `shr_u`, `or`, `wrap`); otherwise `parse` returns `None`, which `build` already turns into `NotCovered` ("outside what the source reading takes").
  - `build` sets `fast = !frag.curried && every position < entry_pos has a record && no record's code holds an Ins::Raw` (recursing into `If`). The last clause keeps a row that reads a closure but still has a `Raw` line elsewhere at `NotCovered` instead of letting it reach `shape_check` as `Rejected(Shape)` (Global Constraints: no census row is `Rejected`). A curried module packs `stage0[idx]`, not `idx`, so reading its closures as positions would give `Rejected(Walk)`; refusing them in the reading covers values and calls alike.
  - `Shape::VarCall{var, args, ..}` with `var < arity` reads as `Apply(Param(arity-1-var), args)`.
  - `Shape::CombinatorCall{root, arity: m, args}` with `args.len() > m` reads as `Apply(Call(Some(pos), args[..m]), args[m..])`.
  - A closed closure value is a `Shape::Combinator{is_rec: false}` with `peel` arity > 0, empty `free_vars` and `pos_of(h) = Some(pos)`. It reads as `Prim("or", Prim("shl", Lit(0), Lit(32)), Lit(pos))`.
    - The guarded Word sites are `Prim`s, so `cps` supplies their guards.
    - The machine's `i32.const 0` and `extend` add no branch (T1), and their value is `def_eq` to `Lit(0)`.
- [ ] **Step 4: `cps` for `Apply`**, in the lowering's order:
  - the `shr_u` site on `cps(head)` and `Lit(32)`, the environment half: guarded like the machine's site, its value unused;
  - `cps_args(args)`;
  - `cps(head)` again, giving `w`;
  - `e.call_dyn(c, app(row_term(w, "wrap"), hw), xs, k)`, where `hw` is the head's word (`w` stays the `&Machine`).
  - `Src` has no `Clone`, so the `Apply` arm inlines the `shr_u` guard on `cps(head)` instead of building a `Prim` node around the head.
- [ ] **Step 5: `build` and `pairing`.**
  - Between `shape_check` and `pairing`: if `call_cycle` over the records finds a cycle, return `NotCovered("the module's calls form a cycle through position {p}")`.
  - `pairing` keeps its one per-record set comparison, widened on both sides:
    - `from_code` is `callees(p, &rec.code, &dynamic_sets(&records))`;
    - `from_source` is `callee_heads` mapped to positions, unioned with `dynamic_set(a)` for each `a` in `closure_call_arities`, then with the record's own position `p` removed, as `callees` removes it.
  - Equal sets guarantee every arm of `call_dyn` finds its callee, so no panic is reachable. A closure call whose set is empty on both sides (as in `twice`) adds nothing to either set; the walk decides it.
- [ ] **Step 6: Cost (D6).**
  - `call_sites` and `cost` gain `width`. `module_cost` passes `|a| dynamic_set(&frag.records(), a).len() as u64` to both of its `cost` calls. The set reads records' `env` and `arity`, never their `Ins`, so `cost`'s rule that padding the code cannot move a verdict still holds.
  - A `VarCall` adds `max(1, width(args.len())) + Σ sites(args)`.
  - An over-applied `CombinatorCall` adds `2 * (1 + Σ sites(head args)) + max(1, width(extra)) + Σ sites(extra args)`.
  - The memo lives for one `module_cost` call.
  - `callee_heads` walks `VarCall` and the extra arguments, and adds no dynamic target.
- [ ] **Step 7:** Run `cargo test -j 10 -p tatic --lib proof::tests`. Expected: PASS.
- [ ] **Step 8:** Run `run.ps1 -Kind gate -Name t4-verdicts -Affinity CFF -Command "cargo test -j 10 -p tatic --lib -- verdicts_match baseline_fixture_matches"`. Expected: against `15ad793`'s run, the verdict diff shows exactly the 8 rows moved.
- [ ] **Step 9: Commit** with explicit paths: `git commit -m "feat: the gate reads closure values and closure calls"`.

### Task 5: Mutants of the closure convention

**Files:**
- Modify: `crates/tatic/src/proof/tests/gate_mutants.rs`.
- Modify: `crates/tatic/src/testing/ins_mutate.rs`. Move `with_record(frag, pos, f)` here from `proof/tests/modules.rs:126` as `pub(crate)`, and point `modules.rs` at it.

How to write each mutant:
- Assert `Rejected` and record the layer (`Walk` or `Kernel`), plus `forged_rejected`.
- Use `check` for edits to the entry, and `check_frag` with `with_record` for edits to any other record.
- Name each edited instruction by its position, never as "the first match".

- [ ] **Step 1: Write the tests.**
  - On `non_tail_closure_carrying_recursion`:
    - Index off by one: in the entry, change the `konst 1` immediately before `Row("or")` to `konst 2`.
    - Halves swapped: change the entry's packing from `i32.const 0; extend; konst 32; shl; konst 1; or` to `konst 1; extend; konst 32; shl; i32.const 0; or`.
    - Closure body changed: in `$c1`, change `konst 1` to `konst 2`.
    - Argument replaced: in `$c0`'s else branch, change the `get 2` (the closure call's argument, pushed after `i32.wrap_i64` of the environment half) to `get 0`. Expected: `Rejected(Walk)`.
    - A closure call dropped (the spec's case, on a non-empty set): in `$c0`, replace the tail `get $p1; Row("wrap"); CallIndirect(1)` with `Row("add")`. Expected: `Rejected(Pairing)`. This overlaps T4's test on purpose.
  - On `twice`, one closure call where the source makes two (the spec's case): replace the inner call's `get` (head), `Row("wrap")` and `CallIndirect(1)` with `Row("add")`, so the outer call takes the inner call's environment half plus argument folded into one word. Its set is empty, so both callee sets are empty. Expected: `Rejected(Walk)`: with both sets empty each call answers `z` at once, so the walk diverges at a guard first: the machine's `add` guard meets the source's `z`, "the machine branches but the source is stuck". This mutant exercises the `shr_u` guards' lockstep, not the dispatch.
- [ ] **Step 2:** Run `cargo test -j 10 -p tatic --lib gate_mutants`. Expected: PASS, with every mutant rejected.
- [ ] **Step 3: Commit.** `git commit -m "test: mutants of the closure convention are rejected"`

### Task 6: Cost, the suites, the docs

**Files:**
- Create: `docs/tier-cycle/15-the-jit-and-the-target-machine/34-closures-through-the-gate.md`.
- Modify: `docs/tier-cycle/README.md` (index line), `PARKED.md`, `docs/TOUR.md`, `ROADMAP.md` (if it names the census steps), and the front matter of the spec and of this plan.

- [ ] **Step 1: Cost.**
  - Write a throwaway probe test and save it as `docs/runs/2026-11-13/patches/q2-cost.patch`.
  - It prints check and build work for the 8 rows and for `capturing_closure_loop`, `straight_line`, `held_out_b`, `doubling(6)`, `doubling(12)` and gcd, by the doc-32 table's method (`p1_probe`).
  - Run it at `15ad793` and at the branch head, each through `run.ps1 -Kind probe -Affinity CFF`.
  - Expected: `doubling(12)` stays under `MAX_GATE_TREE`. Report the work ratio for every accepted row, since the two new `Prog` constructors change every statement.
  - If a dynamic site's work exceeds a static one's by more than the noise, refit `CALL_WEIGHT` as T12 did, and say so.
- [ ] **Step 2: Suites.**
  - Run `run.ps1 -Kind gate -Name q2-suite -Affinity CFF -Command "cargo test -j 10 -p tatic-wasm && cargo test -j 10 -p tatic && cargo test -j 10 -p church-bv"`.
  - Then run the ignored op-table tests: `cargo test -j 10 -p tatic --lib op_table -- --ignored`.
  - Expected: all pass, or each failure is named with its cause. The three older failures known from doc 32 stay as they were.
- [ ] **Step 3: Docs.**
  - Section 34: the verdicts, the mutants and their layers, the cost table and the run ids.
  - `PARKED.md`:
    - Delete "Bit rows (...)" and "`call_indirect` and the table".
    - Restate the row counts of the scratch-local and heap entries against the new verdicts.
    - Add "direct calls into Pointer records" (decision y1), with the trigger "a census row that calls a bare-value combinator directly".
  - `docs/TOUR.md`: add to the glossary and to flow steps 3 and 6 the closure word, the dynamic call (`Ins::CallIndirect`, `dynamic_set`, `dispatch_chain`, `SEnv::call_dyn`), the `Unary` class and `machine/prog.rs`.
  - Set the front matter of the spec and this plan to `status: done`.
- [ ] **Step 4:** Run every repo guard: `cite_check`, `tour_check`, `front_matter_check`, `layout_check`, `size_check`, `test_placement_check`, `script_header_check`, `stack_literal_check` and `doc_index_check`. Expected: ok.
- [ ] **Step 5: Commit.** `git commit -m "docs: closures through the gate, the finding and the docs"`

## End-state fit

| change | where | replaces | deletes |
|---|---|---|---|
| Prog meanings in their own module (T0) | `machine/prog.rs` | half of `machine.rs` | nothing |
| the rows and `Unary` (T1) | `encoding/gates.rs`, `ops.rs`, `wasm.rs#table`, `machine.rs#Class`, `prog.rs` | `Raw` closure-word lines | PARKED "Bit rows (...)" |
| `Ins::CallIndirect`, `dynamic_set`, the widened `callees`, `dispatch_chain`, `call_dyn`, `call_cycle` (T2) | `machine.rs`, `prog.rs`, `statement.rs`, `sim.rs`, `print.rs` | `Raw("call_indirect ..")`; `closed`'s own `path` cycle check | PARKED "`call_indirect` and the table"; `closed`'s `path` parameter |
| the lowering emits rows; type lines derived; `curried` (T3) | `lower_wat.rs`, `compile.rs` | `Lowering.call_indirect_arities` | that field and its pushes |
| `Src::Apply`, the closure value, `Reading.fast`, cycle `NotCovered`, widened pairing, D6 cost (T4) | `proof/gate.rs` | the "outside what the source reading takes" refusal for these shapes | nothing |

## Calls this plan made (for review)

- **`call_indirect` is a new constructor, not `Call` reading its index from the stack.** The static table picks with `eq_bv` at literal indices, and the walk cannot branch on that at a run-time index. Putting every static call on a `choose` chain would add a machine branch the source lacks. Both reviewer rounds re-tested this rejection and it holds.
- **One `CallIndirect` constructor for all arities, its arity a literal operand.** The meaning picks the arity's chain with `eq_bv`, which reduces by conversion at the literal, exactly as `Ctxt::table` does for a static index. Rejected: one constructor per arity (a module-dependent `ctor_list`, so `Prog`'s type would vary per module).
- **The dispatch test is the encoding's `eq_bit(n)`, not the `eq` row by name,** so a table without `eq` (the toy table) still builds every meaning, and no new function is added.
- **The dynamic set has one builder, `dynamic_set` (and `dynamic_sets` over it), on bare `Entry`s.** `Ctxt` holds the sets for the statement; `proof_open`, `closed` and the gate call it where no `Ctxt` exists.
- **The frame width covers closure-call arities,** so a call wider than every record builds its callee frame and answers `z`. Both sides build their chain with the one `dispatch_chain`, so `Src::Apply` carries no set.
- **The closure value's source term is `Prim("or", Prim("shl", Lit 0, Lit 32), Lit pos)`.** Unary sites add no branch and their value converts, so there is no `Src` node for `extend` or `wrap`.
- **`call_cycle` is a precheck and the only cycle detector.** `closed` drops its `path` check. `Ctxt::real` keeps its assert as an invariant, so `statement` stays infallible. Making it fallible would mean propagating errors out of `c.lam` closures, where `Real` is built, and touching 6 callers.
- **The reading refuses closures unless `Reading.fast`,** set from a new `CompiledFragment.curried` (the registry's dispatch choice) and "every position before the entry has a record". A curried module with no bare value has no extra slots but still emits `Raw` dispatch, so a slot count alone would give it `Rejected(Shape)`. Folding it into the reading covers closure values and calls with no separate refusal step.
- **`pairing` compares widened callee sets** (source: static heads plus each closure call's dynamic set; code: widened `callees`). Equal sets make `call_dyn`'s lookups total, so a source closure call with no counterpart cannot panic. One closure call where the source makes two, on an empty set, is left to the walk (`Rejected(Walk)`).
- **`call_cycle` runs between `shape_check` and `pairing`,** since it reads only code.
- **Decision y1 keeps a refusal.** The lowering does emit direct calls into `Pointer` records with the environment pushed first (`lower_wat.rs`, the known-call arm), so `Call` would pop one word too few. Generalising `Call` to drop the environment word was weighed: it needs the arity table to carry `(arity, env)` through `shape`, `seq_step`, `Ctxt.arities` and `check_code`, and changes `Call`'s meaning for every statement.
- **Shift rows are width-generic** (`log2 n` stages), and tests of the halves run at n = 64.

## Review log

- **Round 1** had three Sonnet reviewers: spec coverage, tests, and fewer concepts. They found:
  - The curried refusal, based on slot count, misses curried rows that have no bare value (critical).
  - Pairing had no dynamic half, which left a panic.
  - The dynamic set was computed in two places.
  - Adding a `Vec` would break `MeaningEnv`'s `Copy`.
  - T0 would break the visibility of private methods.
  - Decision y had no representation; it is now y1, refuse.
  - `arg_ranges` used the wrong arity for nested calls.
  - The head-once test could not live in gate.rs, whose items are private; it moved to the sim mirror.
  - The T2 controls did not assert `hc`.
  - `\f. f 1` was left in the NotCovered list.
  - Several `cargo test` lines passed more than one filter.
  - `with_record` was in the wrong place.
  - Several counts were wrong: 34 goldens, `[Ctor; 9]`, 18 cases, 2 `call_sites` call sites.
  - There would have been three cycle detectors.
  - It also proposed fused rows (`pack(pos)`, `env_half`) in place of `shl`, `shr_u` and `or`; that is put to the user as a Decide group.
- **Round 2** had two fresh Sonnet reviewers: consistency, and fewer concepts. They found:
  - A single `CallIndirect` meaning could not know its arity (critical); now the arity is a literal operand picked by `eq_bv`.
  - The `eq` row looked up by name would panic for the toy table (critical); now `eq_test(n)`, with a toy-table test.
  - The cycle test could not reach `call_cycle` behind `pairing`; `call_cycle` now runs first, and the test uses a compiled term with a fallback.
  - No `drop` instruction exists; the mutants use `Row("add")`.
  - The arity-multiset pairing was module-wide and missed the over-applied arity; it is replaced by per-record widened callee sets.
  - `proof_open` and `closed` have no `Ctxt`; `dynamic_sets(module)` serves them. `MeaningEnv` and `SEnv` gain lifetimes; `G::bm` and `G::bs` gain a parameter.
  - `source_fn`'s extra `bool` and the separate refusal folded into `Reading.fast`.
  - `SEnv::callee` extracted so `call_dyn` binds `kont` once; `dispatch_chain` shrank to a fold.
  - The spec did not mention the pairing change or the refusal (y1); it is updated.
  - Smaller: the pap test must shift `pos` and sources; the z-controls name a fuel; `edit_call_site`'s callers; a row-presence check in `parse`.
  - The fewer-concepts reviewer re-judged the fused rows and recommends them for this step; the plan keeps the general rows as the recommended option (see the hand-over's Decide group).
- **Round 3** had two fresh Sonnet reviewers: code-grounded feasibility, and consistency with the spec. They found:
  - A closure call wider than every record would trip `frame`'s assert (`\f. f 1 2`); `widen` now covers `CallIndirect` arities, with a test.
  - `Reading.fast` was said to be set by `build` while `source_fn`'s signature stayed unchanged; `source_fn` now takes `fast`.
  - `dynamic_sets` and `call_cycle` took `ModEntry`s, which `build` lacks before the sources exist; they take `&[Option<&Entry>]`.
  - `pairing`'s source set kept the record's own position, which `callees` drops, so a self-arity closure call would be `Rejected(Pairing)`; it is now removed, with a test.
  - The cycle test's term captured `x`, so the reading would refuse it before `call_cycle`; it is now closed.
  - The argument mutant named the wrong `get`; it is now `get 2` in `$c0`'s else branch. The `twice` mutant's stated reason was wrong; it fails at the guards.
  - `eq_test` duplicated the existing `eq_bit`; dropped.
  - `cost` (gate.rs:200) also needs `width`; the source's closure-call arities get one walker, `closure_call_arities`.
  - The spec still placed `callees`/`call_cycle` in `statement.rs`, said the Unary mutant test "skips by name", called y "pending", and its Risks missed that `CallIndirect` changes every statement; all fixed.
- **Round 4** had one fresh Sonnet reviewer checking round 3's fixes against the code. It confirmed them, and found:
  - The wide-call test could not fail (position 1's arity 3 already set `fw = 3`); it is now `CallIndirect(4)` (important).
  - The self-arity pairing test's `with_record` fallback could not change the source; it now compiles `\x. (\f. f (\z. z + 1)) (\y. y 1)`.
  - `arg_ranges` is private; it becomes `pub(crate)`.
  - `w` named both the machine and the head word, and `Src` has no `Clone`; the `Apply` arm inlines the guard.
  - A closure-reading row with a `Raw` line elsewhere would turn `Rejected(Shape)`; `Reading.fast` now also requires no `Raw` line.
  - The `twice` mutant's branch is the machine's `add` guard.
  - It proposed holding the dynamic sets on the widened `Machine` beside `fw`; put to the user as a Decide group.
  None of these changes the design; round 5 was not run.
