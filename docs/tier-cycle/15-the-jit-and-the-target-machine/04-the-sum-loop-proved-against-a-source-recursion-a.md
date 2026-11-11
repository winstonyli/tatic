### The sum loop proved against a source recursion: a spike (2026-11-10)

The question: before a v0.8 spec puts loops through the gate, can the kernel prove an emitted `loop`/`br` list equal
to a source-side recursion, and how should that recursion be stated? Target: the loop in
`tests/golden/partial_application_loop_specialised.wat` (p0 = x, p1 = acc, temporaries t0 and t1 at addresses 2 and 3),
written as `Ins` by hand. Throwaway; patch at `docs/superpowers/spikes/2026-11-10-sum-loop-spike.patch`, reverted.

**It proves, and it is cheap.** The statement is a fuel-matched simulation, for every fuel `N` with `GoodNat N`, every
answer type `R`, exit continuation `k0`, timeout answer `z`, start `x`, `acc` and memory `mu0`:
`M sum N R (\st mu. k0 st) z s (upd 1 acc (upd 0 x mu0)) = N (V -> V -> R) (\x acc. z) Bsrc x acc`, with
`Bsrc = \g x acc. choose (le_s x 0) (k0 (acc, s)) (g (x - 1) (acc + x))`. The source is the same step unrolled by the
same fuel, in the answer type. The proof is `GoodNat`'s induction on fuel: the motive quantifies over `x`, `acc` and the
memory under the frame (it grows by the two temporaries' stores each turn); the base is `refl z`; the step is one J
that pushes the hypothesis through the shared `choose`. `conv` did the rest: it reduced the loop body's loads through
the `upd` chain at literal addresses with no lemma. Run `2026-11-10-sum-loop-spike` (untimed, one run, 10% load):

| check | n = 4 | n = 24 | n = 64 |
|---|---|---|---|
| simulation (proved) | 2.3 ms | 3.3 ms | 6.9 ms |
| no-temps program against its own source (proved) | 1.2 ms | 2.1 ms | 5.8 ms |
| `sub` for `add` (rejected) | 1.0 ms | 2.0 ms | 3.8 ms |
| no-temps program against the sum's source (rejected) | 0.6 ms | 1.0 ms | 4.5 ms |
| run by `refl`: 3 from 0, fuel 4, answers `k0 (6, s)` | 1.9 ms | 3.5 ms | 10.4 ms |
| run by `refl`: fuel 3 times out | 0.4 ms | 0.6 ms | 2.3 ms |

The runs answering 5, or exiting at fuel 3, are rejected too. The no-temps program assigns `x` before reading it for
`acc`, so it computes `acc + (x - 1)`. Against the sum's source it is rejected; against that sequential source it is
proved, so the rejection is semantic, not an artefact of the proof's shape.

What it settles for a "loops through the gate" milestone (a v0.8 candidate; ROADMAP picks none yet):

- **How to state the source recursion:** as the source step unrolled by the machine's own fuel, in the answer type.
  Termination, `Ev` and value facts then belong to the source side only, and J transfers them. No relational
  big-step form was needed. The `Ev`-relational form was weighed as the fallback and not run.
- **The existing `loop_law` is not enough** (inference from its statement, not run): its invariant ranges over the
  stack only and `Good f` quantifies over every memory, so the body's first `Load` is stuck. A general loop law must
  take an invariant over (stack, memory), as this proof's motive does.
- **Continuations must ignore the frame.** With a general `k : G T` the two sides differ in the junk left in memory
  (the frame and temporaries), so an `Id` cannot hold. The spike restricts to `\st mu. k0 st`. A function's return
  ignores its locals, so this fits; the other way is a relational statement.
- **One J per `br` site**, through the `choose` that guards it. gcd and the two-`br` loops would need one each.
- **`local.set` has no `Ins`.** The lowering emits it as `Ins::Raw` (`crates/tatic/src/jit/lower_wat.rs`, the
  `local.set $t{i}` and `$p{i}` lines), and the machine's `Store` takes the address under the value, so the spike
  wrote `push i; <value>; store`. v1 needs a `LocalSet(i)` instruction, or a lowering that pushes the address first.

