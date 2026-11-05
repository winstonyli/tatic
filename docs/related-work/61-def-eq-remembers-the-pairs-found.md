## 61. `def_eq` remembers the pairs `==` found unequal

§59 left one quadratic in `conv`. It tries syntactic `==` before reducing
at every level, which is what lets it skip equal subterms (§56, §57).
On two right-nested chains `f (f (... x))` that differ only at the
bottom, every level's `==` fails, and each one walks down to the bottom
again. Two 8,000-deep chains took 23 s in a debug build.

**How other checkers avoid it.**
- *Lean 4* caches a structural hash in every `Expr` node, so `==` on
  unequal terms usually fails at the first hash. Its kernel also keeps a
  union-find of terms already proven equal, and a cache of pairs whose
  definitional equality failed.
- *Coq*'s conversion tests only physical (pointer) equality on
  subterms, not structural `==`, and compares reduced terms lazily on
  stacks. There is no repeated `==` walk, but also no skipping of equal
  subterms that aren't shared.
- *Agda* runs a syntactic check before conversion, but not at every
  level.

**Options.**
- *A. A structural hash in every node* (Lean).
  - Pros: `==` fails fast everywhere, not only in `def_eq`.
  - Cons: every constructor and pattern in the kernel changes. By far
    the largest option.
- *B. A hash per pointer, cached in `ReductionCache`.*
  - Pros: no representation change.
  - Cons: every node `def_eq` compares gets hashed and inserted, even
    when the sides are equal, which is 95% of calls from `infer` (§55).
- *C. Pointer equality only below the top* (Coq).
  - Pros: removes code.
  - Cons: equal subterms that aren't shared get reduced again, which
    undoes §57.
- *D. Note the pairs a failing `==` found unequal,* for the rest of one
  `def_eq` call.
  - Pros: no cost when the sides are equal. A failing `==` notes one
    pair per level on its failing path, and exactly those pairs are the
    ones `conv` recurses into next.
  - Cons: a set of pointer pairs in `ReductionCache`.

**Built: D.** `eq_noting` is `==` that inserts each unequal child pair
into `ReductionCache::unequal` on its way back up. `conv` uses it for
the top-level `==`. `conv_rc` skips `==` for a noted pair and otherwise
uses `eq_noting` too. Keys are `PtrKey`s, which hold their `Rc`s, so an
address can't be reused within the call. A noted pair is exactly one
that `==` would reject, so skipping it changes no answer.

The constructor match that `PartialEq`, `conv_whnf` and `eq_noting` all
need is now one function, `same_shape(x, y, c)`: same constructor and
index, then `c` on each pair of children. Each of the three passes its
own `c`.

**Tests.**
- `def_eq_is_linear_on_a_chain_that_differs_at_the_bottom`: the
  8,000-deep chains, under 500 ms in a debug build. It fails under
  either mutation: dropping `conv_rc`'s check of the set (36 s), or
  dropping the insert (30 s).
- `def_eq_agrees_with_comparing_normal_forms` (§57) still holds on its
  20k random pairs, and the kernel fuzzers pass.

**Measured.** Another session's job held the machine, and criterion's
noise column ran from -63% to several hundred percent, so the proof
benches' A/B says nothing either way. An interleaved spike (reverted)
toggled between the old and new `conv` in one binary and took the best
of 20 to 40 alternating rounds. The two non-tail instance proofs and
the `if`-between-closures instance proof were within 3% of the old
`conv`, in both directions across two runs. The fix costs nothing
measurable on the corpus, which has no deep chains.

