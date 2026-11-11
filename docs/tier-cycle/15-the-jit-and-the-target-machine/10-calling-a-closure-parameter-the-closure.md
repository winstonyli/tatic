### Calling a closure parameter: the closure convention against its source, a spike (2026-11-10)

The question: five class C terms call a closure they receive as a parameter (11 `twice`, 17 `iterate`, 27, 32, 33;
census in `docs/decisions/2026-11-10-v08-shape-and-any-backend.md`) and install today on no proof at all. Can the
lowering's convention be proved modularly: the function for every closure related to a source function, and a concrete
closure related to its source lambda, separately? Throwaway; patch
`docs/superpowers/spikes/2026-11-10-closure-spike.patch`, which applies on top of the call-ins spike's patch;
reverted.

**The machine change.** A closure is one word: the table index in the low half, the environment pointer in the high
half (`twice.wat`). `Ins::CallIndirect` is a tenth constructor that pops the argument and the closure word, splits the
word with two bit-rewiring circuits (the real 32-bit halves at n = 64), and runs `table idx env arg mu k`, with `table
: V -> V -> V -> Mem -> (V -> Mem -> R) -> R` a new interpreter parameter. The lowering's `i64.shr_u 32` and
`i32.wrap_i64` are not rows: `wrap` is unary and every row is binary, so the split lives in the constructor, and the
spike's code (`LocalGet 0, LocalGet 0, LocalGet 1, CallIndirect, CallIndirect` for `twice`) does not print as the
golden WAT.

**The closure relation is a hypothesis of the statement**, like the induction hypothesis of a direct call:
`CR(c, f) = Pi a h km ks. (Pi y h'. km y h' = ks y) -> table (lo c) (hi c) a h km = f a ks`, for the source function
in continuation-passing form `f : V -> (V -> R) -> R`. The `twice` law is: for every table, `f`, `c`, `x` and
continuations related as above, `CR(c, f)` implies that the machine's `twice` on `(c, x)` equals `f x (\y. f y ks)`.
Its proof is two applications of the hypothesis, the inner call's relation being the hypothesis at the outer call,
with the machine's continuations written exactly as it builds them (no eta). The other side: a table whose entry 1 is
the compiled body of `\v. v + 1`, built through `prog`, satisfies `CR` for the word `(1, env 2)` and `\a ks. ks (a +
1)`; and the two compose to `twice` on that closure equals `ks ((x + 1) + 1)` (not `x + 2`, which needs an
associativity lemma, not tried).

**`iterate` (17) needs a callee that returns the caller's heap.** Its loop keeps locals in heap cells, and after the call
the machine's continuation reads and writes them, so `km y h' = ks y` fails for an arbitrary `h'`. With `CRp`, the same
relation where the callee hands back the heap it was given, the loop proves in the sum loop's fuel-matched style
against a source recursion, and the `+ 1` closure, whose table entry restores the caller's heap, satisfies `CRp`. The
loop's invariant frame is in the order its stores leave the cells, not the gate's, and the two are equal only
extensionally, so connecting this to the gate's statement needs a heap-extensionality step (not done).

Run `2026-11-10-e2-closure-spike` (untimed, one run, 48% load), n = 64 (n = 4 and 24 give the same verdicts):

| check | build + check |
|---|---|
| the split: `lo c` is the index (proved) | 0.2 + 0.4 ms |
| `twice` law (proved) | 0.4 + 4.3 ms |
| `+ 1` closure satisfies `CR` (proved) | 0.9 + 3.4 ms |
| `twice` on it is `(x + 1) + 1` (proved) | 0.9 + 5.6 ms |
| `+ 1` closure satisfies `CRp` (proved) | 0.4 + 1.5 ms |
| `iterate` law under `CRp` (proved) | 2.4 + 10.9 ms |
| `iterate` on the `+ 1` closure equals the fuel-`N` source (proved) | 2.2 + 9.6 ms |
| run by `refl`: two iterations of `+ 1` from 5, fuel 3, answers 7 (proved) | 0.7 + 14.6 ms |

Rejected, each with a type mismatch whose first 100 characters show only the inferred `Id`, and each one change from a
proved variant: the high half as the index; `twice` calling `f` once; the inner call's argument `f x + 1`; the halves
swapped in the machine's split; a table entry computing `v + 2` against the `+ 1` relation, and composing with it; the
`iterate` run claiming 8; `iterate` testing `n < 0`, calling `f` on `n`, or dropping the call.

What it settles, and what stays open:

- **The higher-order part of goal 1 has a shape**: a closure parameter is a relational hypothesis of the function's
  statement, discharged where the closure is made. Nothing else in the generator's picture changes: a closure call is
  one more call edge whose callee's law is a hypothesis instead of the induction hypothesis.
- **Heaps.** Plain `CR` lets the callee change the heap and then requires the caller to ignore it; `CRp` requires the
  callee to change nothing. Closures whose environment is a record in memory, and anything that allocates, need the
  middle: a relation between the heap before and after (the caller's cells and the record intact), in the counter
  spike's `Inv` style (reasoning, not tried). Locals kept out of the heap would remove the caller's-cells part.
- **Term 27** (`\f. f 1 + f 1 2`) uses `f` at two arities, so the lowering calls it curried, and the result of `f 1` is
  used both as a number and as a closure. A relation between a word and a first-order function cannot say that; it needs
  a relation indexed by type, or one over a universal value domain (reasoning, not tried).

