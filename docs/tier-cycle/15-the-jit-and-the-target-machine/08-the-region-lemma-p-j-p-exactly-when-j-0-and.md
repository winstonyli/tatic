### The region lemma: `p + j = p` exactly when `j = 0`, and offset `k = 2` (2026-11-10)

The question, left by the section above: can `eq (p + j) p = false` be proved for a symbolic offset `j`? Throwaway;
patch `docs/superpowers/spikes/2026-11-10-region-spike.patch`, which applies on top of the call and frame spikes'
patches; reverted.

**No overflow hypothesis is needed.** Modulo `2^n`, `p + j = p` exactly when `j = 0`, so the lemma is an equation
with no hypothesis: for all `p`, `j` with `GoodBv` witnesses, `eq (p + j) p = eq j 0`. Any `j` with `eq j 0 = false`
then gives `false` by one transitivity step. The proof opens both witnesses, one inside the other, with the
`bool_lemma` motive trick, and walks the bits once, so its size is linear in `n`. With `A_i` and `B_i` the prefix
conjunctions of the two `eq`s and `c_i` the carry, the invariant is `A_i = B_i` and `and B_i c_i = false` (while `j`'s
low bits are all zero, the carry is zero). Each step uses two four-variable bit equations proved by splitting every
variable (`lemma_k`, a generalisation of `lemma2`), and the hypotheses enter only by rewriting with `cong1` and
`trans_proof`. That is forced: an `Id(Bool0, true, false)` cannot be turned into a proof of another `Id`, because
`Bool0` is not a valid motive type for its own eliminator, so there is no ex falso to lean on.

**Offset `k = 2`.** Proved directly, it needs exactly the two splits the section above inferred, bits 0 and 1;
splitting either alone is rejected. It also follows from the region lemma at `j = 2`, since `eq 2 0` converts to
`false`. The frame law with a callee that writes `y + 2` proves with either lemma.

**Cancellation**, which disjointness of two cells at symbolic offsets needs: `eq (p + i) (p + j) = eq i j` also
proves, with the invariant `A_k = B_k` and `and B_k ci_k = and B_k cj_k` (the two carries agree while the offsets'
low bits agree) and four bit equations of up to six variables.

Run `2026-11-10-d1-region-spike` (untimed, one run, 79% load from another build, so times are rough):

| check | n = 4 | n = 64 |
|---|---|---|
| region lemma `eq (p + j) p = eq j 0` (proved) | 0.5 + 1.5 ms | 13 + 48 ms |
| `eq (x + 2) x = false`, bits 0 and 1 split (proved) | 0.1 + 0.5 ms | 0.7 + 10.6 ms |
| the same from the region lemma (proved) | 0.2 + 0.8 ms | 7.3 + 21.6 ms |
| frame law, callee writes `y + 2`, `k = 2` lemma (proved) | 0.6 + 2.1 ms | 4.1 + 13.2 ms |
| the same with the region lemma (proved) | 1.0 + 1.7 ms | 4.8 + 27.2 ms |
| cancellation `eq (p + i) (p + j) = eq i j` (proved) | 1.0 + 6.0 ms | 515 + 116 ms |

Times are build + check. Rejected, each with a type mismatch whose first 100 characters show nothing beyond the
`Id` being compared: the region proof against `= false` (false at `j = 0`), against `eq (p + j) j = eq j 0`, and
against `sub` for `add` (a true statement, but not this proof's); the region chain with the carry invariant replaced by
`refl false`; `refl` against the true statement (conversion alone does not decide it); bit 0 or bit 1 split alone for
`k = 2`; three frame-law programs (callee writes `x`, caller reads the callee's cell `x + 2`, the `k = 1` lemma for a
`k = 2` callee); and cancellation against `= false`, against `= eq i i`, and `refl`.

- **The region lemma grows linearly** (8.5 ms check at n = 24 in a quieter iteration run, 20-48 ms at n = 64).
- **Cancellation grows faster** (about `n^2.6` from n = 24 to 64; 16.5 + 221 ms at n = 64 in the quieter run). Its build
  is most of that in the recorded run. One inference, not isolated: a subterm reused at every step is rebuilt or
  rechecked rather than shared.
- **What a heap-allocating calls milestone still needs** is now the region statement itself (an invariant over the
  cells a recursion allocates) and the generated proofs, not a lemma.

