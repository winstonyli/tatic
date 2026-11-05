## 64. Design note: constants, free parameters, and cached loose ranges

§50 to §63 each memoised one thing (`infer`, `def_eq`'s unequal pairs,
the witness) or worked around one copy (`Anchored`, `Params`, §62's
prepass). This note asks whether one change covers them all. It
measures two candidates with a throwaway spike, before any trusted code
changes. The design is in
`docs/superpowers/specs/2026-09-25-kernel-constants-and-loose-ranges-design.md`.

**The root cause.** Postulates are de Bruijn variables at the end of
the context, so every proof term has free variables. Whenever the
context grows under a term, the term is shifted, and `shift` and
`instantiate` rebuild every node they visit. So a DAG comes back as a
tree. Every memo so far has been a way to shift less often.

**How other checkers avoid it.**
- *Lean 4.* Globals are `Expr.const name levels`, looked up in the
  environment, so adding one shifts nothing. Every node caches an
  `Expr.Data` word holding its hash, its loose bound-variable range and
  some flags. `instantiate`, `liftLooseBVars` and `lowerLooseBVars`
  return a subterm unchanged, by pointer, when its range shows there is
  nothing to do. The kernel's type checker keeps its caches (`infer`,
  `whnf`, failures, an equivalence union-find) in one state for a whole
  declaration. Hash-consing (`ShareCommon`) is an opt-in pass, not part
  of the kernel.
- *Coq.* Globals are `Const` and `Ind` by kernel name, locals are `Rel`
  (de Bruijn). Nodes cache nothing. `Constr.map` returns the original
  term when no child changed, so a lift keeps sharing where it does
  nothing, but it still walks the term. It hash-conses each constant's
  body once, when it's added to the environment, since the environment
  keeps it. Nothing here keeps a proof
  term (the JIT stores only a `ProofStrength` per `Hash`), so that has
  no counterpart yet.
- *Agda and Idris 2.* Globals are `Def` or `Ref` by name, locals
  de Bruijn. None of them uses a variable for a global.

**The candidates.**
1. *Constants plus cached loose ranges* (Lean's pair). Postulates become
   `Expr::Const(level)`. Each heap node caches one more than its largest
   free `Var`, so `shift` and `instantiate` keep closed children by
   pointer.
2. *Hash-consing.* One global table, so equal terms are one node, and
   `==` is a pointer compare.
   - Pros: sharing everywhere, and `def_eq`'s equal-sides test in O(1).
   - Cons: a shift still copies, since the shifted term is a different
     term. Postulates still shift, so `Anchored` and the prepass stay. It
     needs a table every constructor goes through.
3. *One checker state for a whole check.* One `ReductionCache` shared
   by every `def_eq` and `whnf` inside a top-level `check`, alongside
   §63's `InferCache`.

**The spike** (a throwaway worktree).
- A kernel-local `Rc<T>` wrapping `std::rc::Rc<Node<T>>`, where
  `Node { loose: u32, val: T }`. It keeps every pattern and
  `Rc::new`/`ptr_eq`/`strong_count` compiling unchanged, so only four
  match arms outside the traversals needed a `Const` case.
- `shift` and `instantiate` return a child by pointer when
  `loose <= cutoff`.
- `Expr::Const(l)`, typed by `ctx[l]`, which must be closed.
  `Postulates::get` returns it for positions below the current binder
  scope's start, and `params_and_close` and the other two scopes record
  that start.
- Candidate 3 as a toggle: `InferCache` owns a `ReductionCache`, which
  its `def_eq` and `whnf` calls use.
- A cached structural hash, under a feature flag, to measure its size
  and cost.
- Scope parameters as levels too, as a toggle: `get` returns a `Const`
  for every position, each node also caches its largest level, and
  `close_pi`/`close_lam` turn the scope's levels into `Var`s, keeping
  children below the scope by pointer. This shares one level sequence
  between postulates and parameters, which the spec doesn't keep (below).

All 301 lib tests passed with loose ranges on. With constants on too, the
two that failed build contexts by hand with `Var` postulates, which the
spike's `Const` rule doesn't cover. Every proof test passed.

**Payoff.** `fib(n)`'s instance proof, proved and then re-checked by
`kernel::check`. Best of 3 interleaved in-process rounds. Another
session's job held 7 to 8.5 cores throughout, but the effects are 100×,
not percent.

| `fib(n)` | as today | loose ranges | constants | both |
|---|---|---|---|---|
| 8, prove + re-check | 55 ms | 50 ms | 52 ms | 14.0 ms |
| 12 | 226 ms | 194 ms | 253 ms | 15.6 ms |
| 16 | 1.90 s | 1.49 s | 1.78 s | 18.5 ms |
| 8, DAG nodes | 13,942 | 12,641 | 13,942 | 5,445 |
| 12 | 48,154 | 42,124 | 48,154 | 7,973 |
| 16 | 265,366 | 227,157 | 265,366 | 10,501 |

With both on, the DAG grows by 632 nodes per level of `n`, so it's
linear: 18,085 nodes at `fib(28)`, proved and re-checked in about
35 ms. Each half alone does little. Constants alone still leave `shift`
rebuilding what it walks. Loose ranges alone find almost nothing
closed, since every term mentions a postulate. A second run added the
one checker state (candidate 3). Alone it was slower at every size: +45%,
+26% and +6% at `fib(8)`, `fib(12)` and `fib(16)`. On top of both it was
14.3, 17.0 and 24.7 ms, against 14.0, 16.2 and 21.2 ms without it in the
same run.

**Overhead.**

`cargo bench --bench proofs`, best of 2 rounds, times in µs. *Wrapper*
is the kernel `Rc` with every fast path off, so it measures the cost of
the bigger node alone; *both* is loose ranges plus constants; *+ hash*
adds the cached structural hash. Another session's job loaded the CPU
through part of round 1 (up to 100% after `base` and `wrapper`), so
round 2 carries most of the weight, and differences under about 25% on
the sub-50 µs benches are noise.

| bench | today | wrapper | both | both + hash |
|---|---|---|---|---|
| `gcd_2_leaves` | 1,688 | 1,799 | 505 | 747 |
| `gcd_3_leaves` | 2,999 | 3,256 | 809 | 1,053 |
| `universal_x1` | 1,613 | 1,671 | 569 | 941 |
| `closure_typed_loop_carried_parameter_universal_proof` | 2,653 | 2,548 | 1,199 | 830 |
| `if_between_closures_self_call_arg` | 8,147 | 8,568 | 4,750 | 3,336 |
| `pap_producing_root_self_call_arg` | 6,940 | 9,026 | 5,187 | 2,613 |
| `relational_x10` | 118 | 111 | 99 | 206 |
| `straight_line_refl_proof` | 9.7 | 9.3 | 6.3 | 9.0 |

- The wrapper alone ranged from 10% faster to 42% slower across benches
  and rounds, median about +4%: within noise, so the 8 extra bytes per
  node don't show.
- Both together were 42% to 73% faster on the five proofs over 1 ms, in
  both rounds, and 19% to 25% faster on `pap_producing_root`. No proof
  got slower.
- The hash was mixed: faster than without it on the closure proofs,
  slower on the `gcd` ones and 2× slower on `relational_x10`. With no
  consumer, that's cost and noise, not payoff.

**Parameters as levels too.** With constants alone, the parameters of
`params_and_close` and the other builder scopes are still `Var`s, so
`Params` and `Anchored` stay. The spike's toggle asked whether they can be
levels as well. That is Isabelle's `Const`/`Free`/`Bound` split and Lean's
`const`/`fvar`/`bvar`: McBride and McKinna's free variables by name and
bound ones by index, the locally nameless representation of Charguéraud
and of Aydemir et al., and Kovács's levels for contexts and indices for
syntax.
- No kernel `check` or `infer` ran while a builder scope was open, across
  every `proof::` test, including the debug-only `debug_assert_has_type`
  calls. Every push inside a scope was a local (parameters, the `v`, `e`,
  motive and ih binders, and `push_path`'s premises), never a lazy
  global. So the kernel only ever has to type globals.
- Closing a scope rebuilt 791 to 911 nodes per `fib` proof and kept 334
  to 414 children by pointer, nearly flat in `n`. The builder's own shift
  work fell from 625, 833 and 1,145 nodes to 204, 412 and 724 at
  `fib(8, 16, 28)`. The kernel's stays at 2.6k to 4k, since its binders
  are unchanged.
- 300 of 301 lib tests passed; the other builds `Var` postulates by hand.
- On `fib(8, 16, 28)`, proving and re-checking took the same time as with
  constants alone, within noise.

On the universal proofs it cost nothing measurable either. The table
shows `cargo bench --bench proofs` in µs, as the best of 3 interleaved
rounds on a mostly idle machine (CPU at 1% to 17% around almost every run).
The same config still varied up to 3× between rounds, so best-of is the
only fair summary. An earlier, noisier run seemed to show parameters as
levels 7% to 85% slower, but that didn't reproduce.

| bench | constants | + parameters as levels |
|---|---|---|
| `gcd_2_leaves` | 482 | 489 |
| `gcd_3_leaves` | 811 | 802 |
| `universal_x1` | 495 | 498 |
| `closure_typed_loop_carried_parameter_universal_proof` | 685 | 699 |
| `if_between_closures_self_call_arg` | 2,918 | 2,825 |
| `pap_producing_root_self_call_arg` | 2,176 | 2,176 |

Counting explains why. Closing scopes rebuilt 615 nodes for `gcd`'s
universal proof and 839 for `fib(16)`. The kernel's `instantiate`
rebuilt 3,547 and 34,804 in the same runs. Meanwhile the builder's own
shifting fell from 274 nodes to 4, and from 833 to 412.

The same runs tried Lean's traversal memo. `replace_rec_fn`, which every
`instantiate`, `lift_loose_bvars` and `abstract` in Lean's kernel goes
through, maps (node, binder offset) to its result for nodes with a
refcount above 1, so a shared subterm that mentions the variables being
replaced is rebuilt once and stays shared. Here it was idle. With
constants alone it found 0 hits in 375 lookups (`gcd`) and 5,605
(`fib(16)`); with parameters as levels, 10 in 402 and 59 in 5,760. A
shared node is almost never reached twice in one traversal, and its
timings matched the runs without it.

One shared level sequence works for the corpus, but only because of the
two facts in the first bullet, which nothing enforces: a leaked
parameter would be one more context entry, so an unproven axiom. The
spec keeps two spaces instead. `Free(l)` levels come from a counter that
never reuses one, and the kernel rejects `Free` in `infer` and `check`,
so a leaked parameter is a failed check. Globals are then never
truncated, so a lazy global inside a scope is safe, and the priming that
prevents one can go.

**Allocation.** The spike keeps `Rc`. The alternatives, for a workload
whose proofs are built, checked once and dropped, on one thread, with
memos keyed by node identity:
- *`Rc` with no weak count.* Lean's object header is 8 bytes (a 32-bit
  count plus tag fields), against `std::rc::Rc`'s 16, and nothing here
  uses weak references. That would bring a node back to today's 64
  bytes with both ranges. The cost is hand-written `unsafe` refcounting
  in the trusted kernel, or a dependency (`triomphe` does this for
  `Arc`).
- *`Arc`.* Only for parallel checking. Otherwise it's atomic updates on
  every clone and drop for nothing.
- *A per-check arena of 32-bit ids, hash-consed.* This is nanoda_lib, a
  Lean 4 checker in Rust. Expressions live in an `IndexSet`, so
  allocating one interns it. A pointer's top bit says whether it
  indexes the persistent export-file arena or the arena of the
  declaration being checked, which is dropped once the declaration
  passes. `alloc_expr` looks in the persistent arena first. Each node
  caches `num_loose_bvars` and `has_fvars`, instantiation and
  abstraction keep `(expr, offset)` caches, and unique free variables
  come from a counter that never goes back. Here it would halve `Expr`
  (4-byte children), drop refcounting and the deep-drop machinery, and
  make `==` an id compare and ids free memo keys. The costs:
  - every constructor and pattern goes through a context, across the
    kernel and all of `proof.rs`;
  - garbage stays until the arena is dropped;
  - every allocation is hashed, which the spike's cached hash measured
    as mixed;
  - an id used with the wrong arena silently names a different term.
- *A bump arena with `&'a Expr<'a>` children,* as rustc's `TyCtxt`
  interns types. Lifetimes would reach every proof record and the JIT.
- *A tracing GC,* as Rocq, Agda and Isabelle get from OCaml, GHC and
  Poly/ML. In Rust it's slower than `Rc` and buys nothing, since terms
  have no cycles.
- *A faster global allocator* (mimalloc). It's one line and independent
  of all of the above, but it also changes the allocator under wasmtime.
  Measured in §66: it halves every proof bench.

The kernel `Rc` wrapper puts every allocation behind one type, so the
first and last of these stay local changes later. The arena is the
principled long-term alternative: it gives hash-consing, stable ids for
a proof cache, and free-all together. It isn't needed for linearity.

**Recommendation.** Build the two-space design, in the four stages the
spec sets out: loose ranges, then `Const` and `Free` in the kernel, then
the builder using them, then removing what no longer pays (§62's
prepass, `Anchored`, the priming). Don't build candidate 3, the cached
hash or the traversal memo: none has a measured payoff yet, and the hash
costs 8 bytes on every node. Candidate 2 isn't needed for linearity. What it would still add is O(1)
equality between separately built equal terms, and nothing in the
current profile asks for that.

