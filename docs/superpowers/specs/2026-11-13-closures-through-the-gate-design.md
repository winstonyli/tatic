---
status: draft
---

# Closures through the gate: the closure word and `call_indirect`

## Intent

Goal 1 (`ROADMAP.md`, "Goals") is a JIT on proved equivalence. Of the 40 census rows, 21 are `NotCovered`, and every
one with a fragment is refused at the first step: the source reading takes no closure value ("position N is outside
what the source reading takes"; `docs/tier-cycle/`, "What blocks the NotCovered rows: a census"). The census ranks the
work in four nested steps; this spec is steps 1 and 2: the closure word (packing and splitting it), the source reading
of closure values, and `call_indirect` through the module's table. Scratch locals and the heap (steps 3 and 4, 11
rows) are not in it.

When it closes, the gate reasons about closure values at all, in one mechanism the later steps extend, and the rows
whose code needs nothing more install as proved code.

## Which rows, checked against their code

The census's step 1 and 2 bounds come from the lines alone. A dump of each row's records and WAT (throwaway probe on
`15ad793`, reverted) refines them:

| row | what its code does | in scope |
|---|---|---|
| `twice`, `iterate`, `iterate_creating_a_closure_over_g` | an entry whose parameter is a closure word, called by `call_indirect`; no closure made, no table | yes |
| `closure_typed_loop_carried_parameter_loop`, `non_tail_closure_carrying_recursion`, `branching_non_tail_closure_carrying_recursion` | `$f` packs the closed lambda `\y. y + 1` (`$c1`, env pointer unread) and calls `$c0`, which calls it by `call_indirect` | yes |
| `tail_recursive_loop_with_if_between_closures_self_call_arg` | `$c0` answers a packed closure word from both branches of an `if`; `$f` calls `$c0` twice (once for each half) and calls the result | yes |
| `inconsistent_arity_saturating_instance` (specialised to `if 0 < 1 then 1 + 2 else \v0. 1 + v0`) | the entry's dead branch answers the packed word of `$c0`; no `call_indirect` | yes |
| `oversized_source_with_a_shrinking_step` | tree 8196, over `MAX_GATE_TREE` (8192) | no: refused by the budget whatever the reading takes |

So the target is 8 rows, not the census's 9. For the first three the module has no combinators, so every closure
call's dispatch set (D1) is empty and their statement says only that each closure call answers `z` on both sides,
as wasm traps on it; their acceptance shows the reading takes the shapes, and the proof about closures is in the
other five, where the same function (`iterate`'s loop is `$c0` of `closure_typed_loop..`) runs against a real table.
None of the three installs today (`installs: false`): the host cannot pass a closure. Every in-scope closure is closed (no captures), so every environment
pointer is 0 and no record reads its `$env`; the lowering's packing is `i32.const env; i64.extend_i32_u; i64.const
32; i64.shl; i64.const idx; i64.or`, the split `i64.const 32; i64.shr_u; i32.wrap_i64` (env) and `i32.wrap_i64`
(index), all closures are 1-ary (`(type $ty1 (func (param i32) (param i64) (result i64)))`).

## Goals, non-goals, anti-goals

- **Goal:** the 8 rows' verdicts go from `NotCovered` to `Accepted` and no other row of
  `proof/tests/baseline.rs#VERDICTS` moves. Five of them install today (`installs: true` in the baseline) and then
  install as proved code; `twice`, `iterate` and `iterate_creating_a_closure_over_g` stay uninstalled (their modules
  print `call_indirect` with no table, which wasm does not validate).
- **Goal:** mutants of the closure convention are `Rejected` (list under "Checks").
- **Goal:** one mechanism: a closure call is the module's existing call table entered at a run-time index. No
  per-row or per-shape case.
- **Non-goals:** captured variables (heap records, `$envtmp`, `$papenv`, `local.tee`), partial applications,
  closures over `Rec` combinators, curried calls of a parameter at two arities (the other `inconsistent_arity_*` rows),
  a proof of a higher-order function reusable across modules, folding total-row guards.
- **Anti-goals:** a false accept; a source reading that reads the `Ins` list; a change to the emitted WAT (the
  golden files stay byte for byte); a cost model padding code can game (cost stays read from the source and the
  registry).

## Design

### D1. Both sides read a closure as its word

The source reading takes two new shapes, and nothing else changes in what it refuses:

- **A closure value**: a closed literal lambda (`Shape::Combinator`, non-`Rec`, no free variables, peeling to arity
  `a > 0`) at a position the registry holds reads as its word, built as the lowering builds it: the packing
  `or(shl(extend(i32.const 0), 32), pos)` from the row meanings in the lowering's order, each Word site guarded as
  the machine's is. Settled by the v2 probe (run `2026-11-13-q2-literal-probe`, patch
  `docs/runs/2026-11-13/patches/q2-literal-probe.patch`): the kernel's conversion does reduce the closed packing to
  `lit(64, pos)` (and the split back to `pos` and 0), in under 1.2 ms each, also as the argument of an open head. But
  `Src::Lit(pos)` still fails the walk: `shl` and `or` are guarded Word sites, each a `choose` on the machine side,
  and `machine/sim.rs#Sim::sim_step` requires the source to branch where the machine does ("the machine branches but
  the source returns"). The literal becomes possible once total-row guards are folded (`PARKED.md`); until then the
  built packing mirrors the machine site for site.
- **A closure call**: one `Src::Apply(head, args)`, for an application whose head is a parameter (`Shape::VarCall` on
  a `Var` under the arity) or a call of a closed combinator over-applied by its extra arguments (the lowering's
  `call $cK` then `call_indirect`; `parse` already reads the head as a `Src`). Read in the lowering's order: the head (whose word gives the environment half,
  then is dropped), the arguments left to right, the head again (whose word gives the index), then the dispatch
  below. The head is evaluated twice because the lowering emits it twice (`$f` of the `tail_recursive_loop..` row
  calls `$c0` once for each half); a parameter head is two reads, a call head two calls, and the source is pure, so
  the reading means the same as one evaluation.

**The dispatch.** A closure call can reach the module's *dynamic set* for its arity `a`: the records reached through
an environment pointer (`EnvAccess::Pointer`, the lowering's bare-value combinators, printed with `(param $env i32)`)
whose arity is `a`, computed once from the records. Every combinator sits in the `elem` list, but a direct-only one
is printed `(param $p0 i64) ..` with no `$env`, so its type is not `$ty_a` and wasm traps on a closure call into it
(`$c0` of `non_tail_closure_carrying_recursion.wat` is at table index 0 with three `i64` parameters). So the record's
`EnvAccess`, which decides its printed type, is part of the trusted dispatch semantics. Both sides dispatch on
the index word through the same chain, `(i == p1) (call p1) ((i == p2) (call p2) .. z)`, where `call p` is the
side's existing static call: `SEnv::call` on the source side, and on the machine side the `call` constructor's meaning
at the literal `p` (`Ctxt::table` applied to `p`). Each test `(i == p)` is a `choose` on the `eq` row (the probe `ch`
in the proof), not `Ctxt::table`'s `eq_bv` pick: the walk branches only on `ch`, and `eq_bv` at a run-time index is
stuck. On the source side `i` is the `wrap` row's meaning applied to the
head's word, on the machine side the popped index (itself `wrap` of the word). An index outside the set answers `z`
on both sides, as wasm traps on it: past the table, `$f`'s index, or a target whose type is not `$ty_a` (so the
entry's own position, reachable from `Ctxt::table` by a raw index, is never entered by a closure call unless it is in
the set). This is the precedent of the `mod` row, whose out-of-domain answer is `z` on both sides. The chain binds the
call's continuation once, outside the chain, so its size is linear in the set, never a power of it across sequential
calls.

**Only the fast convention.** The model above is the lowering's `Fast` dispatch (the index is the position, every
table slot a record). A module that also prints partial-application wrappers or curried stages (`Item::Text`
functions at table slots; curried packing puts `stage0[idx]` in the word, not `idx`) has table slots the model does
not see, so a module with a closure call and any such slot is `NotCovered`, decided from the registry (a position
with no record, or the registry's choice of curried dispatch), never from the `Ins` list. The 8 rows are all `Fast`
with every slot a record (dump above).

`pairing` keeps its one per-record comparison of callee sets, widened on both sides: the source's static heads plus
the dynamic set of each closure call it makes, against the code's static targets plus the dynamic set of each
`call_indirect`. A closure value adds no callee (`$f` packs `$c1` and never calls it), and the over-application's
head is a static `CombinatorCall` on the source side and a `call $cK` in the code. Equal sets make every arm of the
source's dispatch find its callee, so a closure call present on one side only is `Rejected(Pairing)` on a non-empty
set, not a panic; on an empty set the walk rejects it (corrected at plan time, round 2).

So a closure call is a branch over the dynamic set whose every arm is a static call, on both sides: the walk's branch
step and call rule cover it. Fuel: the two evaluations of the head are calls at the same fuel, so they give the same
word; the generator applies the callee's law at each. The source must evaluate the head twice too, not because the
values differ but because the walk is lockstep: each machine `call $cK` needs a source call head. The machine's `call_indirect` is either one more `Prog`
constructor whose meaning is that chain, or the existing `call` constructor (which already takes its index as a `V`)
generalised to take the index from the stack through the set's filter; the builder picks, as long as an index outside
the set reaches `z`, never `Ctxt::table` at a raw index. It pops the index, then `a` arguments, then the environment word, which it drops. The callees `cs` of
`Ctxt::table` widen from the static `Call` targets to those plus the dynamic sets of the entry's closure calls.

Considered:

- **The closure relation as a statement hypothesis** (`docs/tier-cycle/`, "Calling a closure parameter: the closure
  convention against its source, a spike"): `CR(c, f)` for each closure parameter, discharged where the closure is
  made. Modular (a higher-order function proved once for every closure), and proved in the spike for `twice` and
  `iterate`. Not recommended: a closure-valued answer (`$c0` of the `tail_recursive_loop..` row, the saturating
  instance's branch), an `if` whose branches are a number and a closure, and a parameter used at two arities each
  need another relation (type-indexed, or `CRp` and a heap middle), where the word reading treats all of them as
  words. Proof reuse across modules is not something the gate does today (it proves one compiled module).
- **Static calls as `Apply` of a literal head** (one call form in the reading): per call arity it needs no padding,
  but every static call would then rest on conversion reducing `wrap(lit p) == lit q`, and `pairing` keys on static
  heads (`callee_heads`). Not taken for this step; once total-row guards are folded and the closure value can be a
  literal (D1), it is a later deletion of `Src::Call(Some(..))`, not rework.

What an `Accepted` verdict claims, then: the code agrees, for every fuel and every input word, with the source read
with each closed lambda as its table word and each application of a word as the table entry at its low half. The
registry's lambda-to-position map is trusted exactly as it already is for callees (`pairing`); the `elem` line is
printed from the same positions and the `$tyK` lines from the same instructions (D4).

### D2. The closure word's rows

- `shl`, `shr_u`, `or`: `Class::Word`, total (`Dom::TOTAL`), each printing its `i64.*` line. Guarded like every Word
  site (the guard fold stays parked).
- `wrap` (`i32.wrap_i64`, the low 32 bits) and `extend` (`i64.extend_i32_u`, the identity on a zero-extended word):
  1 to 1. No class takes one operand, so a `Unary` class with its own `Prog` constructor. A Unary site is
  unguarded (the guard is Word-specific: `binop(guarded=true)` and the source's `Src::Prim`), so it adds no branch on
  either side.
- None of these rows has a source operator (`PrimOp`): the op-table's `PrimOp::ALL` loop does not reach them, so their
  circuits are checked by a direct n = 64 test against `u64`, and the operator-swap mutant test iterates only over the rows `carrier()` can build (those with a `PrimOp`).
- `i32.const`: a `Class::Const` row printing `i32.const k`, its word the low 32 bits of `k`.

### D3. `i32` values are zero-extended words

An `i32` value is a width-n word whose high half is 0; no stack kind tells it apart. `wrap` makes one, `i32.const`
makes one, `extend` and `call_indirect` take one. Wasm's validator types the module, so a list that mixes the kinds
does not install, whatever the gate says of it.

### D4. The `$tyK` lines printed from the instructions

The dispatch (D1) assumes table index `i` is module position `i` and `$tyK` is `(param i32)` then `K` `i64`s.
`lower()` already prints `(elem (i32.const 0) $c0 ..)` from the positions in order (`jit/lower_wat.rs`); the type
lines come from `Lowering.call_indirect_arities`, a side list. With `call_indirect` an `Ins` carrying its arity, the
printer derives the `$tyK` lines from the records' instructions and the side list is deleted, so the printed types
and the modelled ones come from one place.

### D5. Records reached through an environment pointer

`machine::shape_check` admits `EnvAccess::Pointer` records besides `Params(0)`. Such a record prints `$env i32`
first and then `$p{i}` by its arity (`print.rs#print_func`), and `local.get` prints `$p{i}` by name, so the frame's
slots and the printed names agree by construction; no modelled instruction reads `$env` (`local.get $env` and memory
reads stay `Raw`). A direct `call` into a `Pointer` record (the lowering pushes the environment first) is refused by the
shape check (decision y2, parked with a trigger in `PARKED.md`; plan, "Calls this plan made"); none of the 8 rows has one.

### D6. Cost

A dynamic call site enters the table for each position in its dispatch set, so `proof/gate.rs#call_sites` counts a
closure call (`Src::Apply`) as that many call sites, at least one, plus the head's own sites twice (it is evaluated
twice), read from the source and the registry. `CALL_WEIGHT` stays unless the 8 rows' measured work says a dynamic
site costs more than a static one; then refit on a measured probe, as T12 did. Counting one site per closure call
whatever the width was considered: it changes nothing for the 8 rows (width 1), but a wide module would then be slow
instead of `NotCovered`, which is what the budget exists to prevent.

### D7. Cycles

`Ctxt::real` refuses a module whose calls form a cycle (an assert). The dynamic set adds edges: a closure body that
reaches its caller through the table would be one. A precheck `statement.rs#call_cycle`, over the same
widened `machine.rs#callees` that `Ctxt` builds its table from, finds it before any statement is built, and `build` returns it as
`NotCovered`; the assert stays as the invariant the precheck guarantees, so `statement` stays infallible (making it
return `Result` was weighed: `Real` is built inside `c.lam` closures that cannot propagate `?`, and six callers would
change). The set is
derived from the records' arities and `EnvAccess`, which the registry fixes, not from the instructions. A module whose static and dynamic call edges (excluding self-edges, which `Ctxt::table`'s `own` branch
takes as it takes a self-call) form a cycle is `NotCovered`. The dynamic edges over-approximate (every closure call
reaches its whole set), so a module can be refused for a cycle no run takes; that is `NotCovered`, never a wrong
verdict. None of the 8 rows has one.

## Checks

- `VERDICTS`: the 8 rows `Accepted`; a diff of the verdict run shows no other row moved.
- Mutants, each `Rejected` (walk or kernel) and asserted: the packed index off by one; the halves swapped (index
  shifted, environment in the low half); the `call_indirect` argument replaced by another word; the closure body
  `v + 2` against the source's `v + 1`; a closure call dropped; one closure call where the source makes two
  (`twice`).
- Controls (`machine/sim/tests.rs`): a dynamic call on a word whose index is outside the dispatch set answers `z` on
  both sides; one whose target has another arity answers `z`.
- Rows: `wasm.rs#wasm_rows_are_closed_and_typed` covers the new rows (a `Unary` row's meaning infers `V -> V`);
  `jit/op_table_tests.rs` checks their circuits against wasm (`wrap`, `extend`, `shl`, `shr_u`, `or`).
- The golden WAT files unchanged; the O3 statement-mutation tests and the 54 loop-form mutants still pass.
- Cost: check and build work (the doc-32 style table) for the 8 rows and the accepted rows, before and after;
  `doubling(12)` stays under `MAX_GATE_TREE` and its work within the noise of the counted runs.

## End-state fit

| change | where | replaces | deletes |
|---|---|---|---|
| closure value and closure call in the reading | `proof/gate.rs#parse`, `#cps`, `Src` | nothing (new cases of the one reading) | the "outside what the source reading takes" refusal for these shapes |
| source dynamic dispatch | `machine/statement.rs#SEnv` | nothing | nothing |
| `call_indirect` | `machine.rs#Ins::CallIndirect`, `machine/prog.rs#Ctor::CallIndirect` (its meaning a `choose` chain over `dynamic_set`, each arm the static call); `machine.rs#callees` (moved from `statement.rs`) widened | `Ins::Raw("call_indirect ..")` | the `Raw` lines of the 8 rows |
| rows `shl` `shr_u` `or` `wrap` `extend` `i32.const`, class `Unary` | `ops.rs`, `wasm.rs#table`, `machine.rs#Class` | `Raw` lines | the PARKED entry "Bit rows (...)" |
| `$tyK` lines from the instructions | the lowering's printer (`jit/lower_wat.rs`) | `Lowering.call_indirect_arities` | that side list |
| Pointer records admitted | `machine.rs#shape_check` | the `Params(0)`-only rule | nothing |
| the Prog meanings in their own file (after the plan's T0) | `machine/prog.rs` | half of `machine.rs` | nothing |
| cycles as `NotCovered` | `machine/statement.rs#call_cycle`, `proof/gate.rs#build` | the cycle assert as the only guard | nothing (the assert stays as an invariant) |
| dynamic sites in the cost | `proof/gate.rs#call_sites` | nothing | nothing |
| widened callee sets in pairing | `proof/gate.rs#pairing` | static-only sets | nothing |
| direct calls into Pointer records refused | `machine.rs#shape_check` | nothing | nothing (PARKED entry added) |

PARKED: "Bit rows (...)" and "`call_indirect` and the table" are deleted when this lands; the heap and scratch-local
entries stay, their row counts restated against the new verdicts. `docs/TOUR.md` gains the closure word, the
dynamic call and the `Unary` class.

## Left to the builder

- How the generator (`machine/sim.rs`, untrusted) walks a dynamic call: by the existing branch step over the
  dispatch chain, or by one table lemma per module; whichever keeps the walk linear in call sites.
- Settled by the plan (`docs/superpowers/plans/2026-11-13-closures-through-the-gate.md`, "Calls this plan made"):
  the source dispatch is `SEnv::call_dyn`, the instruction `Ins::CallIndirect(arity)`, and `call_indirect` a new
  constructor rather than `call` reading its index from the stack.

## Risks

- **Dispatch width.** A module with many closures of one arity gives every closure call a long chain; the 8 rows
  have one target each. The cost (D6) accounts for it, so a wide module is `NotCovered` before it is slow.
- **The word reading's claim is weaker for closure-valued entry answers.** The saturating instance's entry answers a
  word in its dead branch; an entry whose live answer is a closure would be `Accepted` as agreeing on a word the host
  reads as a number. That is the JIT's behaviour today, not new; the decision "Closure-valued entry answers" accepts it
  as a word.
- **Trusted code grows** by the dispatch (statement, including the set's `EnvAccess` and arity filter), the rows'
  meanings, the `Unary` constructor and the relaxed shape check.
- **A `Unary` constructor changes every statement**: `Prog` gains a binder, so every module's statement and the
  generator change, not only the closure rows'. The cost check (accepted rows and `doubling(12)` before and after)
  measures it. `Ctor::CallIndirect` adds a second binder, with the same effect and the same check.

## Decisions (the user, 2026-11-13)

- **How a closure call is related:** the word reading with a closed-world dispatch (D1), not the spike's closure
  relation `CR` (D1, "Considered").
- **The 1-to-1 rows:** a `Unary` class (D2), not folding the split into `call_indirect` as the spike did (that prints
  differently from the golden WAT, breaking an anti-goal).
- **`i32` values:** zero-extended words (D3), not a `K::I` stack kind checked by the shape check.
- **Closure-valued entry answers:** accepted as words (callees need closure answers anyway, and one rule for every
  position has no special case), not refused at the entry (which would keep the saturating instance `NotCovered`).
