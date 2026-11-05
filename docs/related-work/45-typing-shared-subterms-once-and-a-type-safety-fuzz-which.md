## 45. Typing shared subterms once, and a type-safety fuzz -- which found a crash in the occurs check

This does §44's first two recommendations.

**C1: the memo.** `typing::infer` now memoises a result that is ground
(it has no type variables), keyed by the subterm's hash and its
environment. An environment is numbered by (enclosing environment, the
binder's type node), so the key is O(1) to build. Reuse is exact.
Re-inferring the same subterm in the same environment unifies a fresh
copy of the same constraints. Those succeed again and fix the copy to the
same ground type, so the memo changes no answer. A result that still has
variables isn't memoised. A copy's variables are fresh, and that is what
lets one shared `\x. x` node be used at two types.
`a_shared_lambda_can_still_be_used_at_two_types` pins this: with every
result memoised, it fails.

`\n. t_25`, with `t_{i+1} = t_i + t_i`, now types in about 30 µs, down
from 3.4 s. `a_shared_subterm_is_typed_once` bounds the calls to `infer`
at depth 12 (under 100, where the tree has 8191 nodes) and fails without
the memo. `the_memo_changes_no_answer` runs 4000 random terms with and
without the memo, and requires the two answers to agree on every one.

**D2: the fuzz.** `a_well_typed_term_never_goes_wrong` generates 4000
random terms. They cover every constructor, with subterms reused, dead
branches under constant conditions (including ones that divide by zero),
`Rec` without an `Abs`, and loops. Each is read at arity 0, 1 or 2. For
every term `well_typed` accepts, `eval` at every combination of
`[0, 1, -2, 7, 25]` must give `Ok` or `DivByZero`, never `TypeError`,
`NotAFunction` or `UnboundVariable`. Every generated term terminates, so
`eval` can run on any of them. That is strong normalisation for the
simply typed part, and each `Rec` either can't name itself or is a loop
whose counter goes down by one per self-call from at most 20. Latest
run: 1264 terms well typed, 13984 runs, 189 of them dividing by zero.

Teeth: each of three one-line mutations of the checker fails the fuzz
within the first 200 seeds:
- not unifying `Prim`'s second operand with `Int` (seed 177);
- dropping the rule that `Rec` wraps an `Abs` (seed 20);
- pruning to the wrong branch (seed 86).

**What the fuzz found.** Seed 931 overflowed the stack, with or without
the memo. Reduced:

```
\n. \f. (if n then f else \x. x) (\y. f)
```

The `if` gives `f` the type `a -> a`. The call then needs
`a -> a = (b -> F) -> r`, with `F` the type of `f` itself, so `a` would
have to contain itself. `unify` ran the occurs check only when binding a
variable. Linking one arrow node into another skipped it, which left the
type graph cyclic, and the next `occurs` followed the cycle until the
stack overflowed. So an ill-typed term crashed the process instead of
being declined. The JIT calls `well_typed` on every term it compiles, so
any caller could do that.

The fix runs the occurs check before every link. `occurs` and `ground`
now share one iterative walk with a visited set, so a shared type costs
one visit and no walk recurses. `find` is iterative too. The graph now
stays acyclic, which every later walk relies on.
`an_infinite_type_through_two_arrows_is_declined` is the reduced term;
it overflowed before the fix.

**Why `try_compile` isn't memoised too.** §44 assumed its 73 s came from
an unmemoised walk, as typing's did. Timing each stage at depths 14, 16
and 18 (build, `ir::check`, decompile, lower) shows each one growing
about 4× per two levels, in step with the output: 0.56, 2.2 and 8.9 MB
of WAT. `ir::Node` is a tree with no `let`, so a shared subterm is
emitted once per use. The compiled code is exponential, and no memo on a
walk changes that. The options:

- **Sharing in the IR.** A `Let` node, or a scratch local per shared pure
  subterm, emitted once and read at each use.
  - Pros: compiled code linear in the DAG.
  - Cons: it changes `ir.rs`, `check`, `lower_wat.rs` and `decompile.rs`
    (which would rebuild the shared term through the store's hash
    consing), and the proof walkers are tree walks too. A subterm can be
    bound once only where its first evaluation comes before every use. A
    subterm shared across `If` branches, or under a lambda, can't just be
    hoisted, since that could evaluate a division by zero or a loop the
    term never reaches.
- **A size gate.** Decline to compile a term whose tree size, computed
  with a memo over the DAG, exceeds a bound, and interpret it instead.
  - Pros: a few lines, and compile cost becomes linear in the bound.
  - Cons: `eval` walks the tree too, so such a term stays slow; the gate
    only stops the compiler costing more than the term.
- **Leave it.** No term in the corpus comes near.

The size gate is done in §47.

