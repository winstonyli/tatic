## 59. `whnf` keeps a stuck term's own pointers

This fixes the quadratic cost §57 found. On a stuck application
`whnf_impl` returned `App(Rc::new(whnf(f)), a)`, with a fresh `Rc` for
the function part even when `f` was already stuck and unchanged. `nf`
and `conv` then asked for that fresh `Rc`'s weak head normal form, missed
the pointer-keyed `ReductionCache`, and walked the spine below it again,
once per level. `J`, `WRec` and `SigRec` on a stuck target did the same.

Measured in a debug build before the fix (the test build):

| depth | `nf` of a stuck left spine | `def_eq` on two left spines, differing at the head | `def_eq` on two right-nested chains, differing at the bottom |
|---|---|---|---|
| 500 | 0.40 s | 0.86 s | 50 ms |
| 1,000 | 2.4 s | 4.0 s | 109 ms |
| 2,000 | 11.0 s | 22.0 s | 398 ms |

**Survey.** Other kernels keep a term's pointer when reduction leaves it
alone.
- Lean 4's `update_app`, `update_binding` and friends return the
  original expression when every new child is pointer-equal to the old
  one, and `whnf_core` caches its results.
- Coq's `Constr.map` returns the original term when no child changed.
- Hash-consing makes the question moot, since equal terms share one
  allocation, but it changes every constructor (§50).

**The change.** A new `whnf_step` returns `None` when its argument is
already in weak head normal form. `whnf_rc` then returns the argument's
own `Rc`, and the stuck cases rebuild a node only when a child actually
changed. `ReductionCache.whnf` stores `Rc<Expr>`, and `nf_rc` gets the
weak head normal form through `whnf_rc`, so it's cached too. Reducing a
result again then returns the same pointer and hits the cache after the
first visit. A spike also cached each fresh result as its own weak head
normal form, which turned out to be redundant: no test or mutation could
tell it apart, so it was dropped.

**Tests.**
- `whnf_keeps_the_stuck_part_it_was_given`: for `App`, `J`, `WRec` and
  `SigRec`, the stuck head or target in the result is the same `Rc` it
  was given.
- `nf_and_def_eq_are_linear_on_a_stuck_spine`: `nf` of two 2,000-deep
  spines, one with a redex for its head, and `def_eq` between them, in
  under 500 ms in a debug build. It took 36 s before.
- Mutation caught: `whnf_rc` returning a copy of an unchanged term fails
  both tests (32 s). Copying only a newly reduced head costs O(1) per
  level, and no test catches it, rightly.

**Measured.** The proof benches didn't move beyond their noise column:
§57's inputs never had a deep stuck spine. The fix only matters for
terms that do.

**Left alone: `conv`'s `==` on right-nested chains.** The third column
above is a separate, smaller quadratic. `conv` tries `==` at every
level, and on `f (f (... x))` against `f (f (... y))` each level's `==`
walks down to the bottom again. It's 50 times cheaper than the `whnf`
one, and far outside the corpus's term depths.
- Lean 4 avoids it with a structural hash cached in every node, so `==`
  fails fast. That's a representation change.
- A smaller fix would remember, within one `def_eq` call, the pointer
  pairs `==` already found unequal. That's about 30 lines of trusted
  code.

Neither was built without a term that needs it. §61 later built a
third option: noting the pairs a failing `==` found unequal.

