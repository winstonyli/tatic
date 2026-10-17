---
status: done
---

# Rule mining over an axiomatic theory (commutative ring): prototype spec (draft 3, 2026-10-10)

Status: the spikes ran on branch `ring-spikes` (parked, not merged; 11e081d); the port to rings is parked (`PARKED.md`). (V) = read in the code this session; (U) = unverified.

## Goal
Test whether the self-improving loop (mine rules batch by batch, serve a law stream, metric M = laws needing a heavy proof) is generic, or only works for Church bit-vectors. Domain: a commutative ring given only by axioms. First targets: `(a+b)(a+b) = a*a + 2ab + b*b`, `(a-b)(a+b) = a*a - b*b`, the identities Pythagoras-by-coordinates needs. Pythagoras itself is out of scope (needs geometry or coordinates, plus an order/field).

## What exists (V)
- `Postulates::push(ty)` assumes a closed typed constant, checked to be a type; `get(pos)` gives `Const(pos)`; `check`/`infer` run the kernel (postulates.rs:150-250).
- Equality builders: `sym`, `transport`, `cong1`, `cong_n`, `trans_proof` over `Id`/`refl`/`jelim` (postulates.rs:269-373).
- `NatPostulates` (postulates.rs:452+) shows an inductive type can be added; not needed here.
- Search/rewrite side is bit-vector specific: `Term`, `interp`, `OP_INFO.word`, `prove_rule`, `rule_step` build Church-vector proofs (rewrite.rs). The order machinery (`rule_order_ok`, `lpo_greater`, `tie_greater`) works on `Term` shape only and is mostly reusable (U: it reads `OP_INFO.prec` and `OP_INFO.carries`).

## Design
1. Theory: postulate `R : Type`, `plus, times : R -> R -> R`, `neg : R -> R`, `zero, one : R`, and axioms as `Id`-typed constants: assoc/comm of plus and times, distributivity, identities, `plus x (neg x) = zero`. Axiom variables are universally quantified (Pi over R).
2. Terms: reuse `Term` with its op table replaced by a ring op table; `interp` evaluates in Z/2^64 wrapping arithmetic (a ring, so every law of the theory is true in it; the converse fails, so the screen can accept a non-law, never reject a law).
3. Proof of a law: rewrite both sides to a canonical form using axiom instances, each step `cong`/`trans_proof` over a postulated axiom application. Canonical form = the existing AC-normalisation idea (commutative operands in fixed order, right-nested, distribute `times` over `plus`). The result is a kernel-checkable `Id R lhs rhs`.
4. Mining: a pool of conjectures over the ops, screened by `refute`, grouped by behaviour, proved by (3); proved laws oriented by the existing order and added as rewrite rules; loop and M unchanged.

## Falsification spike (do first, about half a day, no merge)
Hand-write, in a throwaway test, the postulates (R, plus, times, 5 axioms) and a kernel-checked proof of `times(plus a b, plus a b) = plus(plus(times a a, times a b), plus(times b a, times b b))` by explicit axiom applications. Pass: `Postulates::check` accepts, in a few dozen lines of builders. Fail or blow-up (e.g. proof terms need dependent shifting that `cong_n` cannot express over a non-Church carrier): stop and record it.

## Adversarial review
Round 1 (contradictions/stale claims): "Z/2^64 is a ring, so the screen cannot reject a law" holds for commutative-ring laws including `neg`; it does not hold if the target adds division or order (out of scope). The claim that the order machinery is reusable is (U): `OP_INFO` is indexed by the 8 bit-vector ops, so the ring needs its own table, or `OP_INFO` made a parameter; that is a refactor of every `OP_INFO[o]` site, not a rename.
Round 2 (missing steps, edge cases): (a) Axiom instantiation needs matching a rule against subterms and building the substitution as `app` arguments; the bit-vector `rule_step` does this with Church witnesses, so the ring needs a new, simpler one (no goodness witnesses, since `R` is abstract). (b) Termination: AC axioms (comm, assoc) are permutative, so the `rule_permutative` per-instance orientation is required, and distribution alone is not terminating with `neg` unless oriented by the weight order (U, needs the same check as the bit-vector case). (c) Mining pool: random terms over 2 ops and 3 variables are mostly screen-true consequences of ring normal form; the interesting measure is how many distinct normal forms the loop needs rules for. M must be redefined: with a complete axiom base, every law is provable by normalisation, so "machine proofs needed" has no ring analogue. The honest metric is proof size or rewrite steps per law, falling as rules are learned. This changes the experiment: the question becomes whether learned shortcut rules cut proof size, not whether a heavy prover is avoided.
Round 3 (payoff): the spike tests only the kernel side; if it passes, the cost of the rest is the table refactor (a), the instantiation builder (b), the new metric (c): est. 2-3 days, mostly new code. If the loop's benefit is only visible with a heavy prover, the ring domain may show nothing; a domain with an incomplete decision procedure (e.g. adding an ordering, or bit-vectors with multiplication) would test self-improvement better. Not designed here.

## Recommendation
Run the spike only (half a day); do not start the port. If it passes, decide on the metric (c) before building more.

## Spike result (2026-10-10): PASSED
`tests/ring_spike.rs` (untracked, 60 lines): postulates `R`, `plus`, `times`, `a`, `b`, `distrib_l`, `distrib_r`; a proof of `(a+b)(a+b) = (a*a + a*b) + (b*a + b*b)` from `distrib_r`, two `distrib_l` instances, `cong_n` over `plus` and `trans_proof`. `Postulates::check` accepts it; the same proof against a wrong target (`aa + bb`) is rejected. Built and run first try, 0.00 s. So the kernel side needs no new builders: the existing `cong_n`/`trans_proof` work over an abstract postulated carrier with no goodness witnesses.
Not tested: comm/assoc axioms (permutative rewriting), matching an axiom against subterms to build the instance automatically, the mining loop, and the metric question (c). Recommendation unchanged: decide the metric before porting.

## Metric options (2026-10-10)
Problem: with a complete ring axiom base, normalisation proves every law, so M (laws needing a heavy prover) has no ring analogue.
Ring-side definitions of M:
- A. Kernel proof size per law. Pro: objective, cheap, falls with shortcut rules. Con: nothing fails; not comparable to bit-vector M; encoding-dependent.
- B. Rewrite steps (axiom applications) per law. Pro: encoding-independent, easy to log. Con: same gap as A; long cheap normalisations mislead.
- C. Kernel check time. Pro: real cost. Con: noisy, mostly tracks size.
- D. Switch to a domain with an incomplete decision procedure (e.g. bit-vectors with multiplication). Pro: M keeps its meaning. Con: abandons the axiomatic-theory goal; multiplication is costly on the carry machine.
- E. Budgeted base prover (bounded-step axiom search); M = laws exceeding the budget. Pro: restores M's meaning, works for any theory. Con: budget is artificial (needs a budget sweep), base search must be written. RECOMMENDED, with B reported alongside; check first that it separates cold from seeded runs, else fall back to D.
Learned / self-play style metrics:
1. Held-out transfer: mine on stream A, measure M (or steps) on unseen stream B over cold-start. Pro: cheap, seeded-vs-cold runs already give it. Con: depends on stream choice; single runs so far.
2. Frontier size: largest law (size/depth) provable within a fixed budget, per round. Pro: capability growth, no fixed stream. Con: needs a bigger-law generator; size is a crude difficulty proxy.
3. Conjecturer/prover self-play: generator proposes laws just over the prover's budget; score = learning progress (frontier speed). Pro: closest to self-improvement, open-ended. Con: degenerates to trivial laws without a novelty filter; biggest build; noisy.
4. Compression (MDL): library size + proofs of the stream. Pro: rewards abstraction, penalises bloat. Con: needs a coding scheme; sensitive to it.
5. Learned search guidance: model scores rewrite steps; metric = nodes expanded per proof. Pro: genuinely learned. Con: training infra and data; far heavier than today.
Aside (diagnostic): per-rule credit (usage x steps saved) shows dead-weight rules.
Plan: 1, then 2 once a bigger-law generator exists, then 3 after the ring base search; 4 as cross-check; skip 5. Caution: all loop figures so far are single runs; use several seeds.

## Metric-E spike result (2026-10-10): separates cold from seeded
`tests/ring_loop_spike.rs` (untracked, ~330 lines, no kernel): commutative-ring terms over a, b, c, 0, 1 with add/mul/neg; axioms = add/mul comm and assoc, left distributivity, `x+0`, `x*1`, `x+(-x)`; a law is proved when a bidirectional BFS over single axiom/lemma applications joins its two sides within a node budget; M = laws not proved. A lemma costs one step like an axiom. Laws = depth-<=2 terms with equal value at 4 points of Z/2^64 (6854 laws, hash-shuffled by salt); candidate lemmas = the batch's unproved laws plus the 35 true depth-<=1 equations; greedy mining (<=6 rounds per batch); seed library = ref mine on the phase-0 stream (12 rounds). Soundness is by the screen only. Test `ring_prover_basics` checks the prover is incomplete exactly where intended (`(x*0)+y = y` needs the lemma `x*0 = 0`).
B=50, K=3, five disjoint streams (stride 11), total M over 5 streams, cold vs seeded:
| budget | salt 1 | salt 2 | salt 3 |
|---|---|---|---|
| 100 | 140 vs 33 | 105 vs 83 | 129 vs 8 |
| 300 | 108 vs 17 | 94 vs 16 | 106 vs 1 |
| 1000 | 103 vs 12 | 93 vs 4 | 103 vs 0 |
So option E has a meaningful M here: cold loops pay mostly in the first batch (e.g. 15,1,4), seeded loops near zero, stable for budgets >= 300; at budget 100 the prover is too weak (salt 2 gap small). Caveats: the stream is dominated by a few lemmas (`x*0 = 0` and zero/neg shapes), so a tiny library removes nearly everything; the candidate pool includes the right small lemmas by construction (the real miner would have to propose them); no kernel proofs, so lemma soundness is only screened. Next if continued: a stream without the zero-law dominance (drop 0 from the leaves), generalising candidates mined from sub-terms instead of a fixed small pool, and kernel proofs for lemmas (the cong_n/trans_proof builders from `tests/ring_spike.rs`).

### Follow-ups 1-2 (2026-10-10; budget 300, B=50 K=3, five streams, total M cold vs seeded, salts 1/2/3)
Leaves a,b,c,0,1 (6854 laws): small-pool candidates 108/94/106 vs 17/16/1; sub-term candidates only (laws + true equations between sub-terms of the failing laws, no fixed pool) 108/94/105 vs 17/16/1: the miner finds `x*0 = 0` and its kin unaided, so the fixed pool is not what makes the result.
Leaves a,b,c,1 (no 0; 2833 laws): 37/23/23 vs 9/5/11 (either candidate source).
Leaves a,b,c only (916 laws, stride 5): 38/33/37 vs 11/1/11 (either source).
So removing the constants removes the zero-law dominance but not the separation: seeded totals stay below cold (ratios .02-.48); the base prover then proves most laws without lemmas (cold M 23-38 of 750), so the signal is smaller and noisier.
