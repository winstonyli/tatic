## Other theories

### Ring-theory spikes (2026-10-10; 8a1df7d, parked, not merged)
Can the loop move from bit-vectors to an axiomatic theory (a commutative ring)? Two throwaway spikes, kept as
`docs/runs/2026-10-17/patches/ring_spikes.patch` (the branch was deleted 2026-11-08); the spec is `docs/superpowers/specs/2026-10-10-ring-theory-prototype-spec.md`.
- **Kernel side, passed** (`tests/ring_spike.rs`). Postulates `R`, `plus`, `times`, `a`, `b`, `distrib_l`, `distrib_r`
  and a proof of `(a+b)(a+b) = (a*a + a*b) + (b*a + b*b)` from `distrib_r`, two `distrib_l` instances, `cong_n` and
  `trans_proof`. `Postulates::check` accepts it and rejects the same proof against `aa + bb`. So the kernel needs no new
  builders over an abstract carrier. Not tested: permutative axioms (comm, assoc), building instances by matching, the
  mining loop.
- **The metric.** With a complete axiom base, normalisation proves every law, so M has no direct ring analogue. Chosen
  option (E): a budgeted base prover, M = laws it can't prove within a node budget.
- **Metric E separates cold from seeded runs** (`tests/ring_loop_spike.rs`, no kernel). Terms over a, b, c, 0, 1 with
  add, mul, neg. The axioms are add and mul comm and assoc, left distributivity, `x+0`, `x*1` and `x+(-x)`. A law is
  proved when a bidirectional BFS over single axiom or lemma applications joins its two sides within the budget; a lemma
  costs one step. The laws are 6854 equations between terms of depth up to 2, equal at 4 points of Z/2^64. Mining is
  greedy (B=50, K=3) over five streams. Total M, cold against seeded, for salts 1/2/3:
  - budget 100: 140/105/129 against 33/83/8 (the prover is too weak; salt 2's gap is small);
  - budget 300: 108/94/106 against 17/16/1;
  - budget 1000: 103/93/103 against 12/4/0.
  - Caveat: a few zero laws (`x*0 = 0` and kin) dominate, so a tiny library removes nearly everything. Lemma soundness is
    only screened, not kernel-checked.
- **Follow-ups at budget 300.**
  - The miner finds `x*0 = 0` and its kin unaided: with candidates only from sub-terms of failing laws, M is 108/94/105
    against 17/16/1.
  - Without 0 (2833 laws): 37/23/23 against 9/5/11. Without 0 and 1 (916 laws): 38/33/37 against 11/1/11.
  - So removing the constants removes the zero-law dominance but not the separation (seeded/cold ratios .02-.48).
    The base prover then proves most laws unaided, so the signal is smaller and noisier.
- **Parked:** porting the loop to rings (table refactor, instance builder, metric E) was estimated at 2-3 days.

