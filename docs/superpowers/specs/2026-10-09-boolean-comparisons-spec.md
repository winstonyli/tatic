---
status: draft
---

# Boolean combinations of comparisons: design spec (draft 3, 2026-10-09)

Status: proposal only, nothing built; parked (`PARKED.md`). Facts marked (V) were read in the code this session; (U) are unverified.

## Problem
On cmp3d the laws that still need a machine proof after the library are mostly two clusters (round-0 stragglers of the seeded phase-0 loop, 24 laws):
negation symmetry (9; now mostly handled by `lt(0,sub(0,x)) -> lt(0,x)`), and offset-by-one laws `lt(add(-1,x), t)` (9). The second is
`x-1 < y  <=>  x != 0 and x <= y`: a conjunction of two comparisons. No short rule exists because a comparison result cannot be combined (V: `lt` is root-only,
returns a one-bit vector `bv_ty(1)`, rewrite.rs:19, encoding.rs:63-83; no Bool negation at Term level).

## Proposal: width-switching Terms (no new operator)
Allow the existing bitwise ops `and`, `or`, `xor` (and constants `0`, `-1`) at the *outside* of `lt`, evaluated at width 1. `Term::eval` currently applies `ops_for(n)` uniformly;
it would take a width: operands of `lt` are evaluated at n, the `lt` result and anything built from it at 1. Then:
- `le(x,y)` = `xor(lt(y,x), -1)` (not lt(y,x)); `nz(x)` = `lt(0,x)`;
- offset law: `lt(add(-1,x),y) = and(lt(0,x), xor(lt(y,x),-1))`.
One mechanism covers every Boolean combination; no per-symbol work (the alternative, a real `le` op 8, covers one symbol for 6-10 h and adds no rules for le-vs-le laws, V from the scoping agent).

## What would change
1. `Term::eval`/`interp`/`plausibly_equals` (rewrite.rs:65-112, V): width parameter; the constants `Zero`/`Ones` mean 0 / all-ones *at their level* (at width 1, `Ones` = 1). Variables occur only under an `lt`.
2. Machine (machine.rs, V: nodes combine operand bits at the same position; `lt` is a carry node whose result is the final carry; `last()` tests that the root is `lt`; `raw_table` zeroes the per-position output when `last()`).
   Generalise "the root is `lt`" to "the root is a Boolean function F of final carries": per-position stepping unchanged, plus a post function F over the final carries of the `lt` nodes. Two `lt` nodes give a product machine (carries add: 2 carries, 4 states).
3. Proofs (rewrite.rs `rewrite`, `rewrite_law`, `rule_step`, `prove_rule`, V: lt-specific at 870, 940-948, 1279-1304; congruence uses `&ops[5]` literally): width-1 terms need `ops_for(1)` for the outer ops and a congruence lemma for `and/or/xor` over lt roots.
4. Pools (search.rs): a restricted family only, e.g. `and`/`xor` of at most two lt atoms drawn from the cmp3 operands. A free product of two lt pools is quadratic in the pool and would swamp the miner.
5. New root rules (the analogues of ltself/ltzero/ltmax), each with a kernel proof; soundness sweeps re-run.

## Adversarial review
Round 1 (contradictions): the first draft said "a new Boolean op"; but `and/or/xor` over width-1 vectors already exist as `ops_for(1)`, so no new operator is needed, the change is the width switch. Also constants: `Ones` at the outer level must be 1, not the n-bit mask (would silently make `xor(lt, -1)` wrong in `interp`).
Round 2 (missing steps): how the proof extracts the final carry as the result and how `moore_encoding` treats a root that is not `lt` is (U): I read `last()` and `raw_table`, not the Moore-encoding consumer. A spike must confirm that a product of two lt machines goes through `add_tree_law` before anything else is built. `carry_cap` (default 10) also bounds the product.
Round 3 (payoff): the cluster is 9 of 24 round-0 stragglers. Even if all were removed, the saving is bounded by their share of the first-batch cost: of M = 54 (seeded phase 0, FAST) the first batch is 24, so at most about 9 of 54 (about 17%), and only if the Boolean rules also keep the later batches' normal forms confluent (U). Rules that rewrite one comparison into a conjunction make the term larger, so they would need a canonical-form argument (the same problem the negation family had before the oriented rule); not designed here.

## Cost estimate
At least 2 days (eval/interp 2 h, machine product + post function 4-6 h, congruence and rule proofs 4-6 h, pools and miner 2-3 h, soundness sweeps and regressions 2-3 h), dominated by the machine and proof-term sites, which assume `lt` is the only width-1 thing. Release rebuild is 21 min per iteration.

## Falsification spike (do first, about 2 h, no merge)
In a throwaway worktree: hard-code one law, `lt(add(-1,x),y) = and(lt(0,x), xor(lt(y,x),-1))`, as a width-1 Term; implement only the width-aware `interp` and the product-machine post function; check that `add_tree_law` proves it at n=4 and `plausibly_equals` agrees at widths 1-6. If it fails or needs more than the sites above, stop and record that.

## Recommendation
Do not build now. Expected gain is at most about 17% of M in the head start, for 2+ days and a risk to the machine prover. Run the spike only if the goal is the kernel extending its own vocabulary; then it is the first step of that path, and the miner would also have to propose width-switching Terms itself.

## Spike result (2026-10-09): PASSED
Throwaway worktree (HEAD 2a4fbef), patch kept at `2026-10-09-boolean-comparisons-spike.patch` (~120 changed lines, 2 files, never merged).
- `Term::is_bool` + width-aware `eval`/`interp` (outer constants at width 1, outer and/or/xor via `ops_for(1)`): rewrite.rs.
- Machine: `fin: Option<Fin>` (Atom(lt node) | K | Bin(op)), `finish<G: Gates>`, `fin_num`; `last()` = `fin.is_some()`; the four final-carry sites in `moore_encoding`/`add_tree_law` (class seed, `dec`, dlemma, `end`) call them; `fin` added to the lemma-cache key. No other site needed (the Round-2 unknown is resolved: the product machine of two lt nodes goes through `moore_encoding` and `add_tree_law` unchanged).
- `lt(add(-1,x),y) = and(lt(0,x), xor(lt(y,x),-1))`: plausible at widths 1-6, proved and kernel-checked at n=4 in 54 ms; the false variant `and(lt(0,x), lt(y,x))` is screened and not proved. All 10 existing machine tests still pass.
- Not done (still the bulk of the 2-day estimate): rewrite.rs rewrite/rule_step/prove_rule congruence for width-1 outer ops (the spike checks laws, not rules), pools, miner proposals, canonical-form argument for oriented Boolean rules, soundness sweeps. The machine part (est. 4-6 h) took under 2 h including the build.

## Status: PARKED (2026-10-09)
Why: the spike shows the machine side is cheap, but the gain is capped at ~17% of M in the head start and the rule side (congruence/rule proofs, pools, canonical forms) is untouched. Revisit when the cmp3d library is the limiting factor, or as the first step if the goal becomes the kernel extending its own vocabulary. Restart point: the spike patch, then hand-write the offset rule through `prove_rule` (half-day probe).
