## 58. `subst_top` drops its `is_var_free` guard

This is §55's third proposal. It turned out smaller than proposed: the
guard wasn't worth fusing, only deleting.

§51 added the guard to skip the old eager `subst_top`, which shifted
the argument in full before looking at the body. Since §53,
`instantiate` walks the body once and touches `s` only at a `Var(d)`.
With `Var(0)` absent, it gives exactly `shift(body, 0, -1)`, in one walk.
So the guard added a second walk, all of the body when the variable was
unused and a prefix when it was used, and saved nothing.
`subst_top_leaves_an_unused_argument_alone` still holds without it.

**Survey.** Kernels that avoid this walk cost differently:
- Lean 4 stores each node's loose-bound-variable range in the node, so
  `instantiate` skips any subterm with no loose variables in O(1). That
  changes every `Expr` constructor.
- Coq's `Constr.map` returns the original pointer when no child changed,
  so substitution keeps unchanged subterms shared. For tatic that would
  also help the pointer-keyed `ReductionCache` and `==`'s pointer
  shortcut.

**Measured** (throwaway spike, reverted). `kernel::check`, best of 9,
with the three versions alternating in one process:

| proof | guard | no guard | no guard, sharing kept |
|---|---|---|---|
| `fib(8)` instance | 56 ms | 55 ms | 54 ms |
| `fib(12)` instance | 406 ms | 428 ms | 403 ms |
| `if`-between-closures instance | 8.3 ms | 7.8 ms | 6.8 ms |

All within noise. After §57, substitution is no longer where these
proofs spend their time. Keeping sharing would cost about 40 lines of
trusted code for at most 10% on one proof, so only the deletion landed.
The bench A/B against §57 showed nothing beyond its noise column either.

