---
status: done
---

# Proof search blended with execution, part 2 (sections 37 onward)

Continuation of `2026-10-01-search-execution-blend-design.md` (sections 0-36; start with its section 0, the current-state summary).
Sections here: 37-53 mining, rewriter and shift work, 54-57 online research for goal D (lemmas uniform in the width), 58-59 the variable `mul` circuit, 60-61 rule promotion and the borrow-bit probe, 62-63 blame localisation and parallel scoring, 64-67 soundness, scaling, proposer pilot, reach, 68-70 a three-variable benchmark with headroom, a rule corpus, a goal-as-lemma baseline, a tie-break for the rule order, a deeper benchmark, 71 the answer-key attempt and faster scoring, 72 checks of the speed-ups on `shr` and a sub-normal-form attempt, 73 a new family (`mix3`), permutative rules and a rule bundle, 74 hand-written base rules plus the miner, 75 the clash found (`subdist`) and the families closed.

## 37. Cross-side mining finds `subdist`; the loop on the shl family; right shifts still not built

**Cross-side candidates** (`RULEMINER_VARS`, default 4). The two-variable pool cannot hold 4-variable laws. A second source
takes a subterm `s` of one normalized side and `s'` of the other with the same value (plain-integer screen at widths 1-4),
abstracts `s` by cutting subterms into up to four variables, rewrites `s'` with the same cuts (placeholders `V(4+j)`, then
renumbered) and keeps it if only cuts remain: the rule `abstract(s) -> abstract(s')`. On the 13 mul stragglers left after
`cancelr`/`cancell` (constants <= 7) it mined `sub(add(x,y), add(z,u)) -> add(sub(x,z), sub(y,u))` (+5) and all 13 are
covered by the chosen rules (the other chosen rules are single-use specializations).

**Out of sample.** Promoting it as `subdist` and rerunning all 246 laws (constants <= 12, cap 14): 246 / 246, machine-free
196 -> 206 (rule instances: `double` 55, `cancelr` 11, `doublechain` 100, `shldist` 205, `cancell` 11, `shldistsub` 31,
`subdist` 37). The wall time (585 s) is not comparable with the earlier runs: total CPU read 90% at the end (other load on
the machine), so only the counts are claimed. Cumulative machine-free share by rule set: none 0 of 246 (all by machine),
shift + double 183, + cancel 196, + subdist 206; the 40 remaining stragglers are the larger constants.

**A different family** (`RULEMINER_FAMILY=shl`, `RULEMINER_LAWS`): the shl miner's 2-variable pool (`shl_conjectures`, now a
function), a stride sample of 305 laws (width-4 equal pairs within the carry cap), proved by `rewrite_law`: 147 are
stragglers (a whole-term machine proof was needed, 32 s base). The miner covers 27 of them with 8 rules, led by
`add(shl x, shl y) -> shl(add x y)` (+10) and `sub(shl x, shl y) -> shl(sub x y)` (+7). Two findings:
- The top rules are the *reverse* of `shldist`/`shldistsub`. Both orientations are sound; the step budget keeps a mixed
  set terminating, but a rule set needs one orientation per law (a rewrite system needs an ordering, here by size would
  prefer the mined direction and the shl-pushing built-ins the other). Not resolved.
- Most uncovered stragglers are constant folding inside shifts and bitwise nodes (`and(shl1(0), shl1(y)) = 0`, `add(shl1 0,
  shl1 0) = 0`), which the miner never targets: its filter keeps only subterms with add/sub and size >= 3. The built-in
  rewriter has no `shl1 0 = 0` or bitwise-constant folding in shift context. So the loop transfers (it finds real, general
  laws) but its coverage here is 27 of 147; widening the candidate filter to bitwise subterms is the next step.

**Right shifts.** Not built; the section 36 classification stands (33 of 190 classes reachable with a shift congruence step).

## 38. Constant folding found by widening the miner; shl-over-bitwise is the next wall

`RULEMINER_ANY=1` lets the pool route abstract subterms without add/sub (size >= 2). On the same 305 sampled shl laws
(147 stragglers) it covers 110 of 147; one rule does most of it: `shl1(0) -> 0` alone removes the machine proof from 92
(and `shl1(shl1(0)) -> 0` from 44, which the first rule subsumes bottom-up). Promoted as the built-in `shlzero`; with it
the stragglers fall from 147 to 55, and the miner (run 2, 132 s, CPU 100% at the end, so timings are contended) covers 22
of those 55 with `sub(x, 0) -> x` (+7), `sub(x, shl1 x) -> sub(0, x)` (+5), `sub(shl1 x, shl1 y) -> shl1(sub x y)` (+3)
and three single-use constant specializations. The same 3-caliber lesson as section 36 holds: the earlier "27 of 147"
was a filter artefact (add/sub only), not a limit of the loop.

**Still uncovered (33 of 55):** shl distributing over the bitwise ops (`and/or/xor(shl x, shl y) = shl(op(x, y))`) and
`xor(x, -1) = sub(-1, x)`. These cannot be added as rules yet: `rule_step` proves rules with `add_tree_law`, whose machine
has no bitwise ops, and `bitwise_law` has no shl (`Term::bit` is position-free; shl at bit i reads bit i-1, so each shl
depth needs its own bit variables in the per-bit lemma). Extending `bitwise_law_k` with per-depth bit variables is the
concrete next step; the rewriter's bitwise branch would then also call `rule_step`.

**Orientation (not resolved).** The mined `sub(shl x, shl y) -> shl(sub x y)` still runs against the built-in
`shldistsub`; `RULE_BUDGET` hides the loop. A fixed order is needed before mined rules go in unattended; proposal: orient
by "shl on atoms" (the built-in direction) and reject mined candidates whose rhs has a shl above an add/sub that a built-in
pushes down. Unbuilt; not tested.

**Not done this round:** the `shr1` step and the lt-family run.

## 39. Generalization scan, step 1: one position-aware prover for bitwise and shift terms

A scan of `tests/church_bv.rs` found six overlaps; ranked: (1) `STerm` (bitwise + shifts of any amount, with `bit_at` and
`shift_law`) duplicates `Term` while `Term::bit` has no shifts; (2) proof routes are hard-wired per call site instead of
dispatched; (3) the five conjecture miners repeat enumerate, fingerprint, group, prove; (4) a rewrite system needs one
term order; (5) the fixed `rewrite` branches (identity, `a + ~a`, `sub(x, 0)`) are rules in all but name; (6) `abstractions`,
`subterms` and `replace_term` are scattered. Items are done one at a time, with a survey first.

**Step 1 (done).** Options: A merge `STerm` into `Term` (`shr1` as op 7, delete `STerm`); B keep both and translate;
C a small `PosTerm` trait (`pos_eval`, `pos_atoms`, `pos_bit`) behind one generic `pos_law`, implemented for `STerm` and
for the add-free `Term`, with `bitwise_law_k` dispatching to it when a shift occurs. C was taken; A stays open (it is C plus
an op and a deletion). Also:
- `prove_rule` proves a rule by `bitwise_law_k` when both sides are add-free (checked), else by `add_tree_law`; `rule_step`
  and the miner's candidate check use it.
- New built-in rules: `shldistand/or/xor`, `notsub` and `notsubl` (`xor(x,-1)`, `xor(-1,x)` to `sub(-1,x)`; the machine proves
  it, the bitwise prover cannot), `shlzero`.
- `rewrite` calls `rule_step` at bitwise nodes, and collapses an add-free term with a shift onto 0, -1 or one of its own
  subterms by the per-position prover (the earlier truth-table collapse treats a shift as an atom).
- Tests: `bitwise_law_proves_shift_laws_and_rejects_false_ones`, `notsub_rule_is_provable`.

**Result.** On the 305 sampled shl laws the whole-term machine proofs needed fall 147 -> 55 (`shlzero`) -> 39 (bitwise
rules) -> 26 (collapse) -> 23 (`notsub`); the miner covers 22 of those 23 (single-use constant specializations
such as `xor(shl1(-1), shl1(shl1(-1))) -> shl1(sub(0,-1))`, not general laws; 1 uncovered). Mul regression with the new
rules: 246 / 246, 206 machine-free, identical rule counts to section 37 (wall 692 s, CPU 99% at the end: contended).

## 40. Generalization scan, steps 2 and 3

**Step 2 (dispatching proof routes): mostly absorbed, not done as a refactor.** `prove_rule` (section 39) is the
dispatcher for rules and for the miner's candidates. The one remaining hand-written cascade is in `conjecture_miner`
(`rewrite_law`, `add_tree_law`, `carry_chain_law`, `bitwise_law_k`), and it reports which method proved each law; a single
`prove_law` would lose those statistics, and `prove_rule` must not call `rewrite_law` (the rewriter calls rules, which would
recurse). Revisit if a new proof route is added.

**Step 3 (shared enumeration): partly done.** `pool_conjectures(pool, n, nv, cap)` groups a term pool by value on all
width-`n` tuples, pairs each member with the group's first, sorts and stride-samples. `lt_conjecture_miner` and
`shl_conjectures` use it (checked: shl run unchanged at 23 stragglers of 305 laws, 22 covered; lt miner 40 sampled laws, 39
proved, 1 without a proof). Not converted: `conjecture_miner`, `shift_conjecture_miner` (it uses `STerm`),
`mul_conjecture_miner`; each has its own pool and proof cascade.

**The lt family in the rule miner is blocked.** `rewrite` has no `lt` (op 5) branch: an `lt` root falls into the bitwise
branch. Running `rule_miner` on lt laws needs an lt congruence step (rewrite both operands, then close with the
`lt` machine proof) first.

## 41. lt in the rewriter, `STerm` merged into `Term`, cumulative rule mining

**lt (item 1).** `rewrite` now has an `lt` root branch (operands rewritten, one-bit codomain via `cong_n(.., bv_ty(1), ..)`,
then `rule_step`); `rewrite_law` closes an `lt` pair by `refl` when the rewritten roots are equal, by operand congruence
(`prove_eq`) when both are `lt`, else by the `lt` machine proof of the rewritten pair (counted in `MACHINE_FALLBACKS`).
Test: `rewrite_law_proves_lt_laws`. A first version rewrote only the operands, so root rules never fired; that was a bug,
visible as 0 of 84 covered.

**Cumulative mining.** Scoring candidates one rule at a time misses laws that need two rules together (both sides of
`lt(x,x) = lt(-1, sub(y,x))` need a rule). `rule_miner` now adds rules greedily on top of the chosen set, a candidate
scored by stragglers fixed (no whole-term machine proof) and then by normalized size removed (`RULEMINER_ROUNDS`, default 8;
about 75 s per round at 47 candidates x 84 laws). A law the rewriter cannot close at all counts as a straggler (fixed
once it is proved machine-free). `RULEMINER_FAMILY=lt` uses `lt` pairs over `lt_pool(2)`; `lt` terms are indexed apart
from the n-bit constants (their 0/1 values would otherwise meet `Zero`); an `lt` rule may keep its size (order: size, text).

**lt result (150 sampled laws, 84 stragglers, 12 rounds, CPU 40-90% over the run):** 24 of 84 covered by 11 chosen rules,
e.g. `lt(x,x) -> lt(-1,-1)`, `lt(add(-1,x), x) -> lt(0,x)`, `lt(0, xor(x,-1)) -> lt(x,-1)`. The rules are sound (each is
proved) but not a canonical form: `lt(xor(x,-1), y) -> lt(add(x,y), x)` is accepted because it scores, not because it is
simpler. The remaining 60 mostly need the same rule family with more rounds, and `lt(x,x) = lt(-1, add(x,y))`-type laws
(operands that are not constants after rewriting). Coverage is still rising per round, so the 12-round figure is a floor.

**`STerm` merged (item 2).** `Term` has `shr1` (op 7: `shr1_op`, `good_shr1`, witness arm, `pos_atoms`/`pos_bit`,
`interp`; `Machine::parse` rejects it, since a right shift reads a later position and is not a left-to-right machine).
`STerm`, `shift_law` and the `PosTerm` impl for it are gone; `shift_k(k, left, t)` builds an amount-`k` shift as `k`
one-bit shifts. The shift tests were ported (new laws: `shr1(or) = or(shr1, shr1)`, `shr n x = 0`); the shift miner
now runs on `Term` through `pool_conjectures` and `bitwise_law_k` (4820 terms, 4207 conjectures proved and checked, 0
rejected). New rules: `shrzero`, `shrdistand/or/xor`. `RULEMINER_FAMILY=shr` (65 laws over the arithmetic pool with
right shifts): 20 unproved, all constant folding; `shr1(0) -> 0` fixes 18, `shr1(shl1(-1)) -> shr1(-1)` one,
`0 = shr1(sub(0,-1))` is left. The 33 reachable shr-over-arithmetic classes of section 36 are not in this pool; whether the
rewriter closes them (through `double` then `shr1(shl1 x) = and(x, shr1(-1))`) is untested.

**Regression.** Mul laws with the final rule set: 246 / 246, 206 machine-free, rule counts identical to section 37
(139 s wall, CPU 39% at the end, so far less contended than the earlier 585 and 692 s runs; the figures still are not
a controlled benchmark).

**Orientation (item 3, not built).** Mined rules are still scored and accepted without a term order; `lt(xor(x,-1), y)`
above shows the cost. A fixed order (shl/shr on atoms, then size, then text) used to reject candidates whose rhs is
larger or equal in that order would make the rule set terminating by construction and let `RULE_BUDGET` go.

## 42. A rule order for the miner; what rules do and do not reach for right shifts

**Order (survey: text tie-break / operator-count weight / full KBO).** `rule_order_ok(l, r)`: no variable occurs more
often in `r` than in `l`, and `r` has fewer operator nodes (a strict drop terminates every rewrite sequence: a substitution
multiplies only variable occurrences that did not increase), or at equal operator count fewer variable occurrences (a
tie-break only, still backed by `RULE_BUDGET`; it admits `lt(x,x) -> lt(-1,-1)`). It replaces the size test and the
`lt` text order in the pool route; cross-side rules may still grow (as `subdist` does) unless `RULEMINER_STRICT=1`.

**Effect.** Mul miner with `cancelr`, `cancell`, `subdist` ablated (91 laws, constants <= 7, 19 stragglers): default
19 / 19 covered, and `sub(add(x,y), add(z,u)) -> add(sub(x,z), sub(y,u))` is rediscovered (+5); with `STRICT=1` 13 / 19
(the growing cross-side rule is refused and its laws need several smaller ones). lt (150 laws, 84 stragglers, 12 rounds):
20 covered under the order against 24 without; the rules are now all non-increasing, e.g. `lt(x,x) -> lt(-1,-1)`,
`lt(xor(x,-1), xor(y,-1)) -> lt(y,x)`, and the arbitrary `lt(xor(x,-1), y) -> lt(add(x,y), x)` is gone.

**Right shifts over arithmetic (`RULEMINER_FAMILY=shr RULEMINER_DEEP=1`, depth-2 pool with sub, every 3rd of the shr
laws, 900 laws).** 98 stragglers; 30 rounds cover 44. The covered ones are constant folding and sub/add cancellations
(`shr1(shl1(-1)) -> shr1(-1)`, `sub(x, add(x,y)) -> sub(0,y)`, ...). The 54 uncovered are the real shr-over-arithmetic
laws, e.g. `shr1(add(y,y)) = shr1(sub(add(y,y), -1))` (a right shift ignores the low bit, which the left side makes 0):
equality of the rewritten sides needs carry reasoning under a shift, which rules over `add`/`sub`/bitwise cannot give,
because `shr1` is not a left-to-right machine. So the cheap route (rules) reaches the part that reduces to bitwise shifts and
constant folding; the rest needs the machine change of section 26 (a lookahead state) or a shr-aware arithmetic lemma.

## 43. A self-matching rule hid the lt result (correction to sections 41 and 42)

**Bug.** A rule whose right side is an instance of its own left side (`lt(x,x) -> lt(-1,-1)`) rewrote its own result
forever: `rule_step` matched `lt(-1,-1)` again. The step budget turned that into "not fixed" in the miner (so the
lt coverage in sections 41 and 42, 24 then 20 then 21 of 84, was a floor set by this bug, not by the rule family), and
without a budget it overflowed the stack (`lt_root_rules_close_constant_false_laws` reproduced it). Fix: `rule_step`
skips a rewrite whose result is the term itself. The scoring measure of the miner is now the rule order's own (operators
x 16 + variable occurrences), which makes `lt(-1,x) -> lt(-1,-1)` (node count unchanged, one variable fewer) score.

**Result (lt, 150 sampled laws, 84 stragglers, up to 30 rounds, converged at 16):** 76 of 84 covered. Three rules do most
of it (+16, +26, +16 fixed): `lt(x,x)`, `lt(x,0)` and `lt(-1,x)` all go to `lt(-1,-1)` (lt is false when the sides are equal,
the right side is 0 or the left side is -1). Promoted as built-ins `ltself`, `ltzero`, `ltmax`. With them the stragglers fall
from 84 to 26 and the miner covers 18 of those 26 (the same 76 + 8 uncovered). The remaining mined lt rules are
non-increasing in the rule order (`lt(add(x,y), x) -> lt(sub(-1,x), y)`, `lt(xor(x,-1), xor(y,-1)) -> lt(y,x)`,
`lt(0, sub(x,-1)) -> lt(x,-1)`, ...). The 8 uncovered laws compare lt terms with different non-constant operands
(`lt(add(x,x), x) = lt(sub(-1,x), xor(x,0))`); they need a canonical form for non-constant lt, which pairwise rules do
not give.

**Other families after the fix:** shl 23 stragglers, 22 covered (unchanged); shr over arithmetic 98 / 44 (unchanged:
those did not rely on a self-matching rule); mul regression 246 / 246 proved, 206 machine-free (123 s wall, CPU not
measured under contention; same rule counts as before the lt rules were added).

**Not done:** a canonical form for non-constant lt; the shr-over-arithmetic laws (section 42 says why rules cannot reach them).


## 44. Rule order as a polynomial weight; ablation from scratch; two experiments that did not pay

**Order.** `rule_order_ok` now compares polynomial weights (`rule_weight`): leaves 1, `shl1`/`shr1` = 2x, other operators
x+y+1. A rule is admitted if each variable's coefficient does not grow and the total weight drops, or ties with fewer variable
occurrences. The operator-count order it replaces treated `shl(x+y) -> shl x + shl y` as growth and, when forced outward
(SHLOUT experiment), the mul family got worse: 245 proved, 148 machine-free, 415 s versus 246 / 206 / ~100 s inward. With the
weight, distributing a shift over a sum is a strict decrease (the shift doubles the whole sum's weight), so the inward
orientation is what the order itself prefers.

**Ablation from scratch (built-ins removed, miner re-derives them, weight order, CPU 12%, Defender RTP off):**
mul MAX=5, 30 stragglers: 28 covered (23 under the old order); mined `shl1(add(x,y),0) -> add(shl1 x, shl1 y)`, `add(x,x) -> shl1 x`,
`add(x,add(x,y)) -> add(shl1 x, y)`, `sub(add(x,y),y) -> x`, `shl1(sub(x,y),0) -> sub(shl1 x, shl1 y)`. shl, 86 stragglers: 79
covered (unchanged). lt, 84 stragglers: 77 covered (76 before). Full mul ablation at MAX=12 is infeasible (candidate cost).
Regression with built-ins: 246 / 246 proved, 206 machine-free, 100 s wall.

**Tried and dropped.** (a) Pair lookahead for non-constant lt (rewrite two lt operands jointly): no coverage change, reverted;
the 8 uncovered lt laws still need a canonical form. (b) SHLOUT orientation: above.

**Not done:** canonical form for non-constant lt; shr over arithmetic (survey of the section 26 machine lookahead versus
accepting bitwise-only right shifts); `conjecture_miner` stays on its own grouping on purpose: it fingerprints terms by kernel normalization (`NfCache`), an
independent check that `Term::interp` matches the kernel, and supports sampled tuples; `pool_conjectures` uses `interp` only.
`mul_conjecture_miner` mines nothing (it runs `mul_laws`), so there is nothing to convert. Decisions on the section 42 shr
survey: accept bitwise-only right shifts (revisit with option A or B when a goal needs `shr1` in a sum); keep the machine
fallback for the 8 non-constant lt laws.


## 45. Per-family miner summary (`scripts/miner_summary.sh`); a correction to the shr numbers

`scripts/miner_summary.sh` prints CPU load and Defender state, then one line per family (mul, shl, lt, shr): stragglers,
covered, wall time. `ABLATE`, `FAMILIES`, `MINER_EXE` pass through. Current rules (CPU 12-29%, RTP off, BelowNormal):
mul MAX=5 4 stragglers / 4 covered; shl 23 / 19; lt 26 / 19; shr (`DEEP=1 MINER_SUB=1 STRIDE=3`, 900 laws, 30 rounds, `ANY=1`) 98 / 48, 632 s (the slow one; `FAMILIES="mul shl lt"` skips it).
`RULEMINER_ANY=1` is required for shr: with `ANY=0` the miner covers 0.

**Correction to my own correction.** A first draft of this section said sections 42 and 43 did not reproduce (88 / 35); that
was the script missing `STRIDE=3` (the laws are every third of the pool, so 900 laws span all of it; without it they are the
first 900). With `STRIDE=3` the baseline is 98 stragglers as in section 42, and covered is 48 (44 then): the weight order and
the lt rules did not hurt, the extra four are new. Sections 42 and 43 stand.

**Ablating the hard-coded rewriter lemmas under the miner** (mul MAX=5 / shl; stragglers, covered):

| ablated | mul | shl |
|---|---|---|
| none | 4 / 4 | 23 / 19 |
| `zero`, `not` | 4 / 4 | 23 / 19 (no effect: no law here needs them after the other rules) |
| `comm` | 11 / 4 | 36 / 19 |
| `assoc` | 13 / 9 (219 s) | 23 / 19 (no effect; lt also 26 / 19) |
| `collapse` | 4 / 4 | 45 / 25 |

Reading: mining recovers `assoc` mostly (9 of 13) and `collapse` partly (25 of 45), but not `comm` (the covered count
does not move: commutativity is an ordering decision in `rewrite`, not an oriented rule; a pair `add(x,y) = add(y,x)` has
no smaller side). So `comm` and ordering belong in the rewriter, not the miner; `zero`/`not` are redundant here.

**Not done:** an open frontier goal (shr over arithmetic, variable multiplication); needs a representation choice (the
section 26 lookahead or a shr-aware carry rule).


## 46. Reach of a carry rule for right shifts (option B measured); design sketch for option A

**Experiment (code reverted).** Two unproved rules, `shr1(x+y) = (shr1 x + shr1 y + (x0 & y0)) & shr1(-1)` and
`shr1(x-y) = (shr1 x - shr1 y - (~x0 & y0)) & shr1(-1)`, with 1 written `~(-1 << 1)` (no new constant needed) and the
mask forced because a truncated sum's top bit is lost (the section 26 point; without the mask the add rule is false:
`x = y = 15`, `n = 4`). Both checked equal to their left sides by `interp` at widths 1..6; proofs were dummies, so this
measures reach only. Shr family (`DEEP=1 MINER_SUB=1 STRIDE=3`, 900 laws): **still 98 stragglers** (base time 1.0 s -> 6.5 s, so
the rules fire). A "straggler" is a law that ends in a whole-term machine proof; the rules turn `shr1(arith)` into arithmetic
over `shr1` atoms, but the two sides still do not become syntactically equal, so the fallback is still needed. Reach: 0 of 98.
(The mined coverage after these rules was not measured: the run was cut at 400 s.)

**Decision.** B as a rule is not enough: it needs a canonical form over `shr1` atoms and a proof of the rules (a carry lemma
at every width), which is most of the work of A. Build A if shr over arithmetic is wanted.

**Sketch of A** (from section 26): `Machine::parse` gives `shr1` a lag (output bit `i` is operand bit `i + 1`, i.e. the
operand's stream delayed by lag 1 on every other operand), the per-position loop runs `n + L - 1` steps and drops the first `L`
outputs, and the last step is a variant step function that forces `shr1` outputs to 0 (the width-`n` truncation), whose
equivalence is a final observation row in `moore_encoding`. Open risk: Moore refinement with a variant last step (the
equivalence holds only for words that end once). Cost estimate: five places; first check is a one-carry case
(`shr1(add x y) = ...` at width 4) built by hand before touching `parse`.

**Tooling.** `scripts/miner_summary.sh` now defaults to mul, shl, lt; `FAMILIES=shr` adds the 10-minute shr run.


## 47. Right shifts without a lookahead machine: the mask reduction (analysis, not built)

**What the 98 shr stragglers look like** (normalized sides from the `STRIDE=3` run, `shr3.out`): 63 are `shr1(A) = shr1(B)`, 19 are
`0 = shr1(A)` (closed `A`, e.g. `shr1(sub(0,-1))`), 11 are bitwise combinations of `shr1` atoms (`and(shr1 x, xor(shr1 x, shr1 y)) = ...`).
In every one the `shr1` arguments are shr-free arithmetic: none has `shr1` inside `add`/`sub`. So 82 of 98 (84%) are root-level
shifts over arithmetic.

**Reduction.** `shr1(t) = shr1(and(t, M))` with `M = shl1(-1)` (all bits but bit 0) is a bitwise-with-shift law, provable by
`bitwise_law_k` (as `shrzero` is). Hence `shr1(A) = shr1(B)` follows from `and(A, M) = and(B, M)`, which has no shift and is a machine
law `add_tree_law` already proves (and over arithmetic); and `0 = shr1(A)` is the case `B = 0`, since `shr1(0) = 0`. The proof is
`shr1 A = shr1(and(A,M)) = shr1(and(B,M)) = shr1 B`: two instances of one rule plus a congruence. No lag, no variant last step, no
change to `Machine::parse`, `core`, or `moore_encoding`: section 26's lookahead is needed only for a `shr1` inside an
arithmetic node, which the data above does not contain.

**Why the section 46 rules failed and this should not:** they rewrote `shr1(arith)` into arithmetic over `shr1` atoms (two sides
still differ, so the fallback stayed). The mask turns the pair into one shift-free machine law instead.

**Plan if built** (needs a go-ahead; estimated one function): in `rewrite_law`/`prove_eq`, when both normalized sides are `shr1(.)`
(or one is 0), prove `and(A,M) = and(B,M)` by `rewrite_law` and wrap with the rule instances; the 11 bitwise-combination cases
follow if the shr rules push shifts to the leaves first. Check: re-run the shr family; stragglers should drop from 98 toward ~16.
The earlier "decide A or B" question is open no longer: neither.


## 48. The mask reduction built (`shr_mask_eq`)

**Built** as section 47 planned: `shr_mask_eq` in `prove_eq` (on the normalized pair) and as the fallback in `rewrite_law` on the
original sides when the normalized pair cannot be closed (the rewriter pushes `shr1` down to atoms such as `shr1(sub(0,-1))`,
which hides the root shifts). The proof is `a = shr1(A&M) = shr1(B&M) = b` with one memoized instance of `shr1 t = shr1(t & M)`
(`prove_rule`, bitwise-with-shift) per side and the congruence of `shr1`; `0` is handled as `shr1 0` through the library rule.
`shr_mask_proves_root_shift_laws_over_arithmetic_and_rejects_false_ones` checks five laws in the kernel at widths 1, 3, 4 and
that laws differing above bit 0 are refused. Suite 35 passed, 35 ignored; mul regression 246 proved / 206 machine-free
(134 s wall under 33% CPU load; 100 s before).

**Result (shr family, `DEEP=1 MINER_SUB=1 STRIDE=3`, 900 laws, one round):** unproved laws 15 -> 0 after the fallback (84 stragglers
with the pair-only hook, 15 of them unproved; 79 with the fallback, none unproved). All 900 laws are now proved; the 79
stragglers each use one machine proof (for `A&M = B&M`), so none is yet machine-free. The 98 stragglers of section 42 were mostly
unproved laws; the old exe does not print the unproved count, so the exact before-figure is not recorded. The miner prints the
count and marks `UNPROVED` rows now. The miner's coverage after the change (30 rounds) did not finish within 580 s and was
not measured.

**Section 47's estimate (98 -> about 16) measured the wrong thing:** it counted laws the rule route cannot finish; the mask
proves them but via a machine law, so they stay stragglers by the miner's definition (needs a whole-term machine proof).
Making them machine-free needs rewrite rules for `and(arith, M)`, i.e. mining over the masked laws: the natural next experiment.

**Not done:** mined coverage of the shr family after the change; machine-free proofs for the 79; section 26's lookahead remains
unneeded for root shifts and unbuilt for a shift inside an arithmetic node (no such law in the pool).


## 49. Mining the shr family after the mask (coverage measured)

Shr family (`DEEP=1 MINER_SUB=1 STRIDE=3`, 900 laws, `ANY=1`, 30 rounds, BelowNormal, 784 s wall, CPU about 30% from other work):
79 stragglers (all proved, none unproved), **36 of 79 covered** machine-free by 20 mined rules, all arithmetic simplifications that
shrink the shifted argument (`sub(x, sub(0,y)) -> add(x,y)` +7, `sub(x, add(x,y)) -> sub(0,y)` +7, `sub(x,0) -> x` +3,
`add(sub(0,x), y) -> sub(y, x)`, `sub(0, xor(x,-1)) -> sub(x,-1)`, ...). The other 43 keep one machine proof for `A&M = B&M`.
Before the mask the same family covered 48 of 98 *with* 50 left unproved or machine-needing; after it every law is proved and 36 + 
the 0-fallback ones are machine-free, 43 are not. That the mask removed the unprovable ones and mining then removes machine proofs is the
split section 48 predicted. Mining the masked laws directly (a separate family of `and(arith, M)` laws) is not built: these
stragglers' normalized forms already contain the arithmetic arguments, which is what the mined rules act on.

**The two bitwise-mix laws are in the kernel-checked test** (section 48's test), so the original-side fallback is guarded.

**Not done:** the 43 uncovered (not listed by the miner; print them with the rule-miner's straggler list minus covered ones to see
whether they need a canonical form for sums under `& M`).


## 50. What the 43 uncovered shr laws are; all families on the mask build

**The 43** (list from the section 49 run): 22 are `0 = shr1(A)` with `A` a closed term whose value is 0 or 1 (`sub(0,-1)`,
`sub(0, or(-1,y))`, `sub(sub(x,-1), x)`, ...): the constant 1 has no shorter form in `Term` (it is `xor(shl1(-1), -1)`), so no rule
can shrink it, and the mask proof closes each with one small machine law `A & M = 0`. The other 21 are `shr1(A) = shr1(B)` with
`A`, `B` different arithmetic terms that agree above bit 0 (`add(x,x)` against `sub(x, xor(x,-1))`, `xor(add(x,y),-1)`
against `sub(xor(x,-1), y)`): equal only through carries, so a machine proof of `A & M = B & M` is the proof itself, not a fallback
that rules would remove. Cost: the 79 stragglers total 1.8 s of build time at 900 laws, about 2 ms each.
**Decision:** leave them; the machine-free target does not apply to laws whose content is carry reasoning.

**All families on this build** (Defender RTP off, CPU 35%, BelowNormal): mul MAX=5 4 stragglers / 4 covered, 0 unproved;
shl 23 / 19, 0 unproved; lt 26 / 19, 0 unproved; shr 79 / 36, 0 unproved (section 49). Identical to the pre-mask numbers for
mul, shl and lt: the mask touches only right shifts.


## 51. Lemma ablation end to end: the encoding search passes it trivially

`encoding_search_rediscovers_library_lemmas_from_statements` proves `add x 0 = x`, `add 0 x = x`, `add x y = add y x`,
`add x ~x = -1` and associativity of add from the statements alone by `add_tree_law` (no rewrite rule, no hand-written invariant),
checks each in the kernel at widths 1, 3, 4, and refuses `add x y = add x x`; 0.22 s. So the section 5 protocol, applied to any lemma
a bit-serial machine can express, is passed by the encoding search; the interesting ablations are the lemmas it cannot express
(right shifts before the mask, variable multiplication, laws needing an unbounded invariant). Section 0 now carries the state
summary (table above the old section 1).


## 52. Variable multiplication: survey and carry-cap measurement (nothing built)

**Measured (throwaway probe, not kept).** `mul x y` at width `n` as partial products, `sum_i (x << i) & -(b_i)` with `b_i` standing in
for bit `i` of `y` as extra variables, parses as a machine with **3n - 2 carries**: n=2: 4, n=3: 7, n=4: 10, n=5: 13, n=6: 16, n=7: 19
(the `shl1` delay cells count as carries). `CARRY_CAP` is 10, so only n=4 fits, with `1 + n` variables; every wider width is over the cap
and the state space is exponential in the carries. Also, a bit of `y` broadcast across all positions is a non-local read: as a
`Term` it needs `shr1` inside a `sub`, which `Machine::parse` rejects (right shifts are root-only, section 48).

| Option | What it is | Pros | Cons |
|---|---|---|---|
| A. New `Term` op for a broadcast bit plus machine support | `bcast_i(y)` | Same pipeline | The bit read is non-local (position `i` feeds every position): not a left-to-right machine; needs a state of `n` stored bits, i.e. carries linear in `n` again |
| B. Partial products with bits of `y` as variables | the probe above | No new op; reuses the machine | 3n-2 carries: at the cap for n=4, over it for n>=5; a variable per bit of `y` |
| C. Case split on the bits of `y`, each case a `mul_const` law | Shannon expansion (like the DD lemmas) | Each case is a constant-mul law already proved machine-free (section 44); cost 2^n cases | Cost doubles per bit; proves per-width laws only; a variable on both sides (`mul x y = mul y x`) also needs cases on `x` and becomes brute force |
| D. Induction on the width or on `y` | `mul x (2y+b) = 2 (mul x y) + b x` | The only route to laws uniform in `n` | The library is Church-encoded per width: the kernel has no induction over `n` here; needs a design change, not a miner |

**Reading.** At a fixed width every variable-multiplication law is finite, and C decides it, so there is nothing for a search to find
beyond the case split. The `n`-uniform statement is the interesting one, and only D reaches it. So the goal "variable multiplication"
is really two goals: C (cheap, per width, brute force) or D (uniform, needs an induction principle). That is the decision for the user.

**lt note (kept for later).** The 7 non-constant lt laws need a canonical form; the borrow-bit encoding (`lt(a,b)` as the top bit of
a bitwise function of `a`, `b` and `sub(a,b)`) would give one now that `shr_mask_eq` exists; untried.


## 53. Goal D (laws uniform in the width): survey of how to get induction over `n` (nothing built)

**Facts from the repo** (bit-vector design doc sections 11-17, kernel `Expr`): the kernel has `W`/`Sup`/`Rec` (a recursor for W types) and
`J`; `Bool` and `Nat` do not compute natively but **Church `Bool`/`Nat` at `Sort0` work and the induction witness
`Good n := Pi P:(Nat->Sort0). P zero -> (Pi m. P m -> P (succ m)) -> P n` is tested** (section 12: `good3 P h0 hs = hs 2 (hs 1 (hs 0 h0))`
by `def_eq`). Today `Bv_n` is a Church tuple of `n` Church `Bool`s, `GoodBv x` is induction over the tuple constructor, and every
law is built per width (`n` appears in the type), with proof size growing about `n^2`-`n^3` (sections 54-57). A uniform law needs a
representation whose width is not in the type structure.

| Option | Representation | Pros | Cons |
|---|---|---|---|
| 1. Church lists of Bools | `Bv := Pi R. (Bool -> R -> R) -> R -> R`, `add` as a fold with a carry (zip by folding into a function) | One law for all `n`; no kernel change; reuses `GoodBool` | New definitions of every operation; zipping two lists needs a function-valued fold, so the induction hypothesis is higher-order; motives end up in `Sort2` (the level walls of sections 12, 16) |
| 2. `W`-type vectors | `W(Bool-tagged, ...)` with the kernel's `Rec` | A real inductive; computes by iota on `Sup` | Heaviest encoding; tags at `Sort2`, child families per constructor; no existing library to reuse; unmeasured kernel cost |
| 3. Bits as a stream, `Nat -> Bool`, with prefix statements | `x : Nat -> Bool` (bit `i`), carries as a stream by Church-`Nat` recursion; a law is `Pi n. GoodNat n -> prefix_equal n (f x) (g x)`, proved by `Good n` induction from the same one-step invariant `moore_encoding` already finds | Reuses the machine and its encodings (the step lemma is the induction step; the base case is the initial state); width is a variable; no kernel change; fits the bit-serial machine exactly | A new representation of values (streams, not tuples): operations are defined as stream transformers; the link to fixed-width `Bv_n` (restricting a stream to its first `n` bits) is a separate bridge lemma; non-local operations (broadcast of a bit of `y`) are still not stream-local, so `mul x y` still needs a second induction over `y` |
| 4. Kernel change: a native `Nat` eliminator over the width | Add `NatRec` to `Expr` | Cleanest proofs | Touches the trusted kernel (`infer`, `whnf`, `shift`, ...); the project has kept `src/kernel.rs` unchanged throughout |

**Recommendation: option 3 as a pilot, in two steps.** (a) Prove `add x 0 = x` and `add x y = add y x` uniformly in `n` over streams
with `Good n` induction, kernel unchanged, and compare its check time with the per-width proofs (sections 17-18). If the one-step
invariant lifts as claimed, the machine search (Moore refinement) gives induction steps for every law it already proves, which would make the
whole pipeline uniform. (b) Only then attack `mul x y` (needs the second induction over `y`'s stream: `mul x (2y+b) = 2 (mul x y) + b x`).
Option 1 is the fallback if streams cannot express the bridge to `Bv_n`. Option 4 only if both fail, and only with the user's go-ahead
for a kernel change.

**Risks to measure first:** Church `Nat` induction at `Sort0` versus the `Sort2` motive that `Id` over `Bool` forces (section 16 level
note); whether `Id` over a `Nat -> Bool` stream needs funext (the kernel has no eta, so prefix equality must be stated pointwise, which is
why the law is `prefix_equal`, not equality of streams).


## 54. Online research for goal D (2026-10-02; sources fetched or taken from search snippets as marked)

**Lean 4 `BitVec` (fetched: Lean API docs for `Init/Data/BitVec/Bitblast`).** Width `w` is a variable in the type, values are numbers mod `2^w`
read through `getLsbD`. Addition: `carry i x y c` is defined by recursion on the bit index (`carry 0 = c`, then majority of the two
bits and the previous carry); `adc` applies the one-bit adder, and `add_eq_adc : x + y = (x.adc y false).snd`. Multiplication:
`mulRec x y s` is the partial-product sum, `mulRec_zero_eq : mulRec x y 0 = if y.getLsbD 0 then x else 0` and
`mulRec_succ_eq : mulRec x y (s+1) = mulRec x y s + if y.getLsbD (s+1) then x <<< (s+1) else 0`; `getLsbD_mul` ties `x * y` to it.
So the uniform multiplication law is an **induction on the bit index `s` of `y`** over whole-vector addition and shifts, not a
bit-serial machine; the step reuses the already-proved addition. This is option D of section 52 done with numbers as the base type.

**Parametric bit-vectors in SMT** (fetched, abstracts only: Niemetz et al., CADE 2019, arXiv 1905.10434, and the SAT 2025 paper on
parametric bit-vectors). They translate to integer arithmetic with `pow2` and uninterpreted functions with inductive axioms;
bitwise operators need axiomatizing (full inductive definition or hand-picked partial properties); add, mul, shifts reduce to
arithmetic mod `2^k`. Results: invertibility conditions previously checked only for widths up to 65 were verified for arbitrary width, and
some rewrites needed manual induction or stayed unsolved (undecidable target logic). The 2025 lazy CEGAR version reports 7,325 of
13,443 benchmarks solved against 2,012 for the baseline; it does not use induction. I could not read the CADE paper's body (the PDF
fetch returned binary), so the per-operator details above are from the summaries.

**Church encodings (search snippets only, not fetched).** Geuvers (2001): induction is not derivable for lambda encodings in the
Calculus of Constructions; Parigot's encoding fixes accessor cost, not induction; Cedille and self types add what is needed. Our
`Good n` witness is the same assumption made explicit (induction as an argument), which is why it works on the unchanged kernel.

**What this changes for section 53.** (1) Evidence for a **numbers-as-base** option, new: represent a word as a Church `Nat` mod `2^n` with a
bit-extraction predicate and prove `mul` by induction on the bit index of `y` as Lean does; it needs a Church `Nat` library (`pow`, `mod`,
division by 2) that the bit-vector design doc (section 11, 17) lists as missing. (2) Streams (option 3) still fit addition, but
`mulRec`'s term `x <<< s` reads `x` at position `i - s`, which is non-local in a left-to-right stream, matching the section 52
finding; Lean sidesteps it by not using bit-serial machines for `mul`. (3) Uniform bit-width reasoning in the literature is done either by
numbers plus recurrences on a bit index (Lean) or by integer arithmetic plus `pow2` axioms (SMT); none of the sources reasons over Church
bit streams.


## 55. Addendum to section 54: the CADE 2019 paper body, read (pdftotext of the fetched PDF)

Niemetz, Preiner, Reynolds, Zohar, Barrett, Tinelli, "Towards Bit-Width-Independent Proofs in SMT Solvers" (CADE 2019, arXiv 1905.10434).
- **Axioms.** Four uninterpreted functions (`pow2`, bitwise and/or as `&N`/`|N`, `~N`) in four modes: *full* (definitions by recursion on the
  width `k`), *partial* (hand-picked properties: base cases, ranges, `&N(k,a,0) = 0`, and extra axioms such as "never even" added after
  inspecting benchmarks), *combined*, *qf*. The full definition of `&N` recurses on the **top** bit: `&N(k,x,y) = ite(k>1, &N(k-1, x mod 2^(k-1),
  y mod 2^(k-1)), 0) + 2^(k-1) * min(ex_(k-1) x, ex_(k-1) y)`, with `ex_i x = (x div 2^i) mod 2`. Width induction here is a recursion that
  peels the high bit and truncates with `mod`, not the least-significant-first order a carry machine uses.
- **Results.** Invertibility conditions: 110 of 160 fully proved, 19 and 17 proved in one direction only; *combined* mode best (104 fully
  proved, 17 unproved), and the quantifier-free base cases alone (*qf*) already do well. LLVM instcombine optimizations: 88 of 180 proved,
  best on the AndOrXor family (pure Boolean reasoning plus ordering), **none of the 9 Shifts-family ones** (bitwise mixed with arithmetic).
  Addition and multiplication are not axiomatized: they translate to integer arithmetic mod `2^k`.
- **Future work they name:** translating the results to a proof assistant (so no kernel-checked uniform proofs there yet).

**Reading for goal D.** (1) The hard cases in the literature are the same family that cost us the most: shifts mixed with arithmetic
(none proved there; section 48 found a reduction for root shifts here). (2) Their uniform reasoning rests on integer arithmetic with `pow2`,
`div`, `mod` as primitives, which is the numbers-as-base route (section 54); in our kernel those are the Church `Nat` library pieces that do not
exist yet. (3) Nothing here gives a kernel-checked uniform multiplication proof; Lean's `mulRec` (section 54) is the closest model.


## 56. How Lean proves `mulRec` (fetched: `src/Init/Data/BitVec/Bitblast.lean`, Lean 4 master, 2026-10-02)

**Definition.** `mulRec x y s` = `mulRec x y (s-1) + cur`, `cur = if y.getLsbD s then x <<< s else 0` (base: `cur` alone).

**The one induction.** `mulRec_eq_mul_signExtend_setWidth : mulRec x y s = x * ((y.setWidth (s+1)).setWidth w)`, by `induction s`:
- zero: case on `y.getLsbD 0`; the truncation of `y` to 1 bit is 0 or 1, and `x * 1 = x`, `x * 0 = 0` (by `simp`).
- succ: rewrite with `mulRec_succ_eq` and the hypothesis, turn the `if` into `x * (y &&& twoPow w (s+1))` (by cases on the bit), merge
  with `BitVec.mul_add` read right to left (distributivity of `*` over `+`), and close with `setWidth_setWidth_succ_eq_setWidth_setWidth_add_twoPow`:
  **truncating `y` to `i+1` bits equals truncating to `i` bits plus `y & 2^i`**.

**The one bitwise lemma** (`setWidth_setWidth_succ_eq...`): `add` becomes `or` because the two summands have disjoint bits
(`add_eq_or_of_and_eq_zero`), then `ext k` and a case split on `k = i`, `k < i`, `k > i` with `omega` for the index arithmetic.
`getLsbD_mul` (`(x*y).getLsbD i = (mulRec x y w).getLsbD i`) is then the case `s = w - 1` of the above.

**What it uses that we lack.** (1) A `mul` already known to distribute over `+` (`BitVec.mul_add`), i.e. `mul` is the number-theoretic product
mod `2^w`, not the circuit; in `tatic` `mul` would be the shift-and-add circuit, so the same step needs distributivity of the *circuit* over `add`
(for constant multipliers this is the section 44 laws, which `add_tree_law` proves; for a variable `y` it is the unproved part).
(2) `Nat` index arithmetic discharged by `omega` (no Church `Nat` solver here). (3) `ext k` on bits, i.e. extensionality over positions: our
`GoodBv` induction (section 17) gives per-tuple induction, and a position-indexed `ext` needs positions as data (a numeral `k` with `Good k`).

**Reading.** The proof has three parts: bit-level truncation arithmetic (disjoint-bit `add = or`, per-position case split), distributivity of
`mul` over `add`, and a plain induction on `s`. In our setting only the second is not already machine-provable at fixed width, and for
that the machine proves it per width for constant multipliers (section 44) but not for a symbolic `y`. That is the real kernel of
goal D: **distributivity of the circuit over a symbolic multiplier**, to be reached by induction on the bit index of `y`.


## 57. The planned "step 1" pilot is vacuous as stated; what a real pilot needs (corrected 2026-10-02)

Checked before building: `tests/church_bv.rs` has no circuit `mul` for two variable vectors (only `mul_const`, a `Term`-level sum of shifts
for a *constant* multiplier). Lean's `mulRec_succ_eq` is `rfl`: the recurrence is the definition, so "prove `mul x (y_low + bit 2^s) = mul x y_low + (bit ? x<<s : 0)`"
here would also be true by definition and test nothing. The content of Lean's proof is the link from the recurrence to a *numeric* meaning of `*`
(distributivity, then the truncation identity).

**Correction (an earlier version of this section said the numeric layer is missing; that was wrong).** `toN` exists: a unary Church `Nat` (`nat_ty`, `nat_lit`,
`nat_add`, `to_n`, `lift_good`), with H4 (`toN (or a b) = toN a + toN b` for disjoint ranges) proved by conversion at n = 2, 4, 8
(bit-vector design doc section 89). What is missing is `Nat` `mul`, `mod 2^n`, and H1 (`toN (add a b) = (toN a + toN b) mod 2^n`).
Design doc section 89 also found that the unary `Nat` does not scale (bit `i` is a numeral of 2^i applications; n = 14 takes 19 ms, n = 16 did not finish in 10 minutes),
and sections 89-90 recommend against building a `Nat` library: state laws over circuits and keep `toN` as an n <= 14 cross-check.

**So goal D's real options are:** (a) at n <= 12, extend the existing `toN` with `Nat` `mul` and a finite `mod`, prove H1 for `add` by case split over bits, then
`toN (mul x y) = toN x * toN y mod 2^n` by induction on `y`'s bit index; it uses the unary layer and stays within its n <= 14 wall; or (b) state the `mul`
laws over circuits only (a partial-product `mul` against commutativity, distributivity over `add`, `mul x 1 = x`), which scales but only compares circuits to circuits and so
tests no numeric meaning; or (c) stop goal D at the survey and keep the per-width machinery, which already proves every constant-multiplier law.

## 58. Goal D option (b) built: variable `mul` circuit laws per width (2026-10-02)

`bits_circuit`, `add_rows`, `mul_bits` and `circuit_law` in `tests/church_bv.rs`: `mul x y` is the shift-and-add partial-product circuit
(`row_i[j] = y_i & x_(j-i)`, ripple-added), a closed Church term of type `Bv_n -> Bv_n -> Bv_n`. A law is proved by, per output bit, case
analysis on all 2n input bits with `refl` leaves, then `cong_n` and the witness eliminations (`k_var_law_to`). Test
`mul_circuit_laws_by_case_analysis_and_false_ones_rejected` proves, at n = 2, 3, 4: `mul x y = mul y x`, `mul x 1 = x`, `mul x 0 = 0`,
`mul x 2 = add x x`, and rejects `mul x y = add x y`.

| n | commutativity (build + check) | all four laws |
|---|---|---|
| 2 | 40 ms | 117 ms |
| 3 | 0.5 s | 1.4 s |
| 4 | 5.4 s | 14.4 s |

(debug build, unshared carries, machine not otherwise loaded or measured; one run.) About 10x per bit: 4^n leaves times n bits, so this is the brute-force
option C of section 52 as a proof, with no uniformity in n and no numeric meaning. It does show the circuit is a correct multiplier for
these laws. Not done: laws with three vectors (distributivity, associativity: 3n bits, n = 3 is 512 leaves per bit), and any width above 4.

## 59. Three-vector `mul` laws, and why the encoding search cannot take the `mul` ablation (2026-10-02)

`circuit_law_k` generalizes `circuit_law` to `k` vectors (sides composed from the two-vector circuits; per output bit a case analysis over `k*n` bits).
Test `mul_circuit_three_vector_laws` proves `mul x (add y z) = add (mul x y) (mul x z)` and `mul (mul x y) z = mul x (mul y z)` at n = 2
(0.76 s for both) and n = 3 (23 s for both, 9 bits, 512 leaves per output bit, debug build, one run, load not measured), and rejects the
false `mul x (add y z) = add (mul x y) z` at both widths.

**Ablation question (next step 3 of section 58), answered by inspection, not a run.** `enum Term` has leaves `V`, `Zero`, `Ones` and ops
`add and or xor sub lt shl1 shr1`; variable multiplication needs a bit of `y` broadcast across all positions, which no op provides
(section 52, option A). The encoding search therefore cannot state a variable-`mul` law, so there is nothing to ablate or rediscover there; the
case split in `circuit_law_k` is the only prover for these laws. The constant-multiplier laws (`mul_const`) are the part the search does cover.

## 60. Promoting mined rules into the library and re-mining (miner survey option A, 2026-10-02)

`PROMOTED` in `tests/church_bv.rs` (parsed by `parse_term` from `Term::show` syntax, cached, rule name `promoted`, `ABLATE=promoted` removes
them) holds the rules the miner chose: 20 from the mul, shl and lt families, then 15 more from the shr second round. Test
`promoted_rules_are_ordered_and_provable` checks each is decreasing in `rule_order_ok` and provable at widths 3 and 4; the suite passes (39 passed, 35 ignored).

Measured with release builds (CPU 57-74% from other sessions, Defender RTP off; counts, not timings, are the result). A straggler is a law
still needing a whole-term machine proof; the miner's "covered" means fewer machine proofs, not none.

| Family | Stragglers before | After promoting the first 20 | Second-round mining |
|---|---|---|---|
| mul (MAX=5) | 4 | 0 | none left |
| shl | 23 | 5 | 0 new rules |
| lt | 26 | 7 | 0 new rules |
| shr | 79 | 76 | 17 rules chosen (15 useful), 33 of 76 covered, 43 uncovered |

**Reading.** One promotion round pays off for the families with small stragglers; a second round finds nothing for shl and lt (a fixed point of
this proposer, pool size 5, at most 2 variables). For shr, the second round's rules are `sub`/`add` identities that replace the machine proofs of 33
laws, but the uncovered set is the same 43 as in section 50, so promotion does not reach them. The shr family was not re-mined after promoting
its own 15 rules (a 12-minute run), so a third round is unmeasured. Not tested: whether promoted rules slow the rewriter on laws outside the
pools (the suite's total time rose from 39 s to 70 s in one run on a loaded machine; not attributed).

## 61. Do promoted rules slow the rewriter? And the borrow-bit probe for the 7 `lt` stragglers (2026-10-02)

**Timing (section 60 loose end).** Debug suite, two runs each, `ABLATE=none` / `ABLATE=promoted`: 59.5 s / 70.5 s, then 82.9 s / 93.1 s. CPU went 41% to 82% over the
runs (other sessions), so the drift is load, not rules; ablating was not faster in either pair. Release, `rewrite_rules_over_the_mul_laws`,
`MULMINER_MAX=7`, two runs each: with the rules 60.4 s and 33.4 s, without 42.3 s and 42.3 s, all 91 laws proved either way, **89 machine-free with the rules, 83 without**.
Conclusion: no measurable slowdown, and the rules remove machine proofs; the times are too noisy (machine 48-82% loaded, Defender RTP off) to rank beyond that.

**Borrow-bit probe (`lt_borrow_bit_probe`, ignored test, width 4).** Restate `lt(a, b) = lt(c, d)` as the shift-free `B(a, b) & TOP = B(c, d) & TOP` with
`B(a, b) = (~a & b) | (~(a ^ b) & (a - b))` and `TOP = 8`. Result for all 7 stragglers: both forms are proved, and **both still need exactly 1 whole-term machine
proof**. So the borrow-bit canonical form does not make these laws machine-free: after the built-in and promoted rules the two `B` terms do not normalize to the
same term, because the laws are carry facts (for example `2x < x` iff the top bit of `x` is set), not rewriting identities. Not tried: a rule set aimed at top-bit
facts; canonical forms at other widths (the probe is width 4 only).

## 62. Blame localisation and real ablation: resolved by existing results (survey, nothing built, 2026-10-02)

The kernel has no metavariables: `check`/`infer` return `Result<_, String>` and every variable needs a declared type, so a hole's type cannot be read from a
kernel error. The designs that remain reduce to existing results: abstracting a lemma as a hypothesis only tests the prover on a known statement
(section 51: the encoding search proves the add lemmas from their statements); builder-level blame (ablate a rule, take the stuck normalized pair, mine a rule)
is what section 45 measured (`assoc` 9 of 13 recovered, `collapse` 25 of 45, `comm` not, an ordering decision). The lemmas left are those no machine
expresses, i.e. laws uniform in `n`, behind the missing induction principle (sections 52, 58).

## 63. Where the miner's time goes, and parallel candidate scoring (2026-10-02)

**Measured (D).** `rule_miner` now prints `RULEMINER time <phase>` per phase. shr family (`DEEP=1 MINER_SUB=1 STRIDE=3 LAWS=900 ANY=1`, release, BelowNormal,
affinity 12 cores, CPU 44-75% from other sessions, Defender RTP off), `ABLATE=promoted` (the pre-promotion state: 79 stragglers, 32 provable candidates): setup
(laws and stragglers) 20 s, candidate generation 0.3 s, provable filter 0.6 s, **19 scoring rounds 1082 s of 1103 s (98%)**, 43-95 s each. With the 35 promoted rules the
same family has 43 stragglers, 1 provable candidate, and the whole run is about 20 s: promotion made the shr mining about 50x cheaper.

**Built (A).** `RULE_BUDGET` and `MACHINE_FALLBACKS` are now thread-local (they were process-global; the miner reads a before/after difference of the latter).
`score` builds its own `ops`/`goods`, and a round scores the candidates on `RULEMINER_THREADS` workers (default 1, clamped to 1..=12, 256 MB stacks), each with
its own `InternScope`; results are folded in candidate order. Same run with `RULEMINER_THREADS=8`: **307 s instead of 1103 s (3.6x)**, the chosen rules
are identical (same hash of the `chosen` lines) and 36 of 79 covered either way. Below the ideal 8x because each worker's memo caches start cold every round
and candidates differ in cost; persistent workers would remove the cold start (not built). Full suite passes.

## 64. Soundness sweep after promotion (2026-10-02)

`family_laws` (factored out of `rule_miner`) feeds the ignored test `soundness_sweep` (`SWEEP_FAMILY`, `SWEEP_WIDTHS`, default 3 and 4). (A) every law plausible at widths 1-6 that
`rewrite_law` proves is kernel-checked at each width; (B) every law equal at width 4 but false at some width in 1..=6 must be refused at that width. Release build, BelowNormal,
CPU 27-78% from other sessions, Defender RTP off, one run per family:

| Family | Laws | (A) proofs kernel-checked | Unproved | (B) false laws | (law, width) pairs refused | Time |
|---|---|---|---|---|---|---|
| mul (MAX=7) | 91 | 182 | 0 | 0 | 0 | 82 s |
| shl (300) | 305 | 558 | 0 | 26 | 52 | 7 s |
| lt (150) | 150 | 294 | 0 | 3 | 3 | 5 s |
| shr (900, `DEEP=1 MINER_SUB=1 STRIDE=3`) | 900 | 1800 | 0 | 0 | 0 | 23 s |

No kernel rejection and no false law accepted. (B) is thin: the mul and shr pools contain no law false at a wider width, so only shl and lt exercise the refusal path.
Meta-test `rule_admission_refuses_wrong_rules`: pairing each promoted left side with every other promoted right side over the same variables gives 426 well-formed
candidates, 35 of them true laws; the admission test (`rule_admissible`: weight order plus provable at widths 3 and 4) refuses all 391 wrong ones. Not covered: widths above 4
(the sweep stops there; the `mul` circuit laws reach n = 4, section 58), and laws outside the generated pools.

## 65. Scaling to wider words (2026-10-02)

Ignored test `scaling_sweep` (`SWEEP_FAMILY`, `SWEEP_SAMPLE`, `SWEEP_WIDTHS`): 20 evenly spaced true laws per family, `rewrite_law` then kernel `check`, then all 35 promoted rules via
`prove_rule`, release build, BelowNormal. **The machine was heavily loaded by other sessions (CPU 32-100% during the runs, Defender RTP off), so times are inflated and noisy; one run each.**
Sums over the 20 laws, build + check seconds:

| Family | n=4 | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|---|
| mul (MAX=7) | 4.9 | 2.8 | 4.8 | 8.5 | not run |
| shl | 0.8 | 0.8 | 1.9 | 3.9 | 12.6 |
| lt | 1.3 | 1.5 | 3.5 | 8.8 | 29.2 |
| shr | 0.7 | 1.1 | 3.0 | 4.5 | 8.3 |
| 35 promoted rules (`prove_rule`) | 0.9-4.0 | 0.7-4.1 | 1.7-5.0 | 4.1-16.4 | 13.0-53.2 (not run for mul) |

All 80 sampled laws per width were proved and kernel-checked at every width tried (n=64 for shl, lt, shr; n=32 for mul), none unproved, and all 35 promoted rules are provable at n=64 (checked
in the sweep for shl, lt, shr runs). Cost grows about 2-3x per doubling of the width (roughly n^1.5; the n=4 cells include one-time cache building), so the per-width machine
and rewriter proofs reach word sizes. Not measured: n=128 (the `interp` evaluator is `u128`), mul at n=64, the `mul` circuit laws beyond n=4 (case analysis, about 10x per bit; section 58), and a clean-machine rerun.

**Rerun (same day, after pushing).** CPU at the start of the four runs 38%, 53%, 40%, 40% (other sessions; never below 20%, so not a quiet machine; Defender RTP off). Sums of build + check seconds
over the 20 laws: mul 3.6, 5.8, 7.7, 10.2, 44.5 (n = 4, 8, 16, 32, 64); lt 0.5, 0.7, 1.6, 3.0, 8.7; shr 0.3, 0.5, 1.0, 2.5, 6.8; shl 0.4, 4.5, 2.1, 10.9, 5.4 (n=8 and n=32 contain single slow
laws, 1.7 s and 5.2 s, that vanish at the next width: load noise). Promoted rules at n=64: 30.0 s (mul run), 21.3 s, 10.7 s, 14.7 s. All 80 sampled laws proved and checked at every width including
mul at n=64. The two lowest-load families (lt, shr; CPU 28-40%) grow about 2x per doubling, so close to linear in the width; the earlier 2-3x was load.

## 66. Proposer pilot, first two proposers against the miner (2026-10-02)

`rule_miner` takes `RULEMINER_PROPOSER` (`mined`, the default, or `random`, `transfer`; `pilot_candidates`). The pilot proposers replace the miner's candidate generator and its
`applicable` prefilter; everything after is shared (rule-order check, `prove_rule` at width 4, cumulative greedy scoring over the same stragglers), so differences in coverage come from the candidate set only.
Target: shr, `ABLATE=promoted` (79 stragglers; `DEEP=1 MINER_SUB=1 STRIDE=3 LAWS=900 ANY=1`), release, BelowNormal, 8 scoring threads, CPU 30-41% from other sessions, Defender RTP off, one run each.

| Proposer | Proposed | Decreasing in the rule order | Provable | Rules that fixed stragglers | Stragglers covered |
|---|---|---|---|---|---|
| `mined` (the miner: abstract straggler subterms, same value at width 4) | 67 (after the applicability filter) | n/a | 32 | 17 chosen, 15 with a fix | 36 of 79 |
| `random` (12768 random rules, size 3-9, variables of the right side among the left's; no value check) | 12768 | 9932 | 535 (4.2%) | 1: `sub(y, 0) -> y` | 3 of 79 |
| `transfer` (the first 20 promoted rules, mined on mul, shl, lt only, each variable replaced by `x`, `y`, `0`, `-1`) | 153 | 122 | 122 (80%) | 1: `sub(x, 0) -> x` | 3 of 79 |

**Reading.** Both pilot proposers reach only the same 3 stragglers (the `sub(x, 0)` fix). The miner's 33 further coverages come from rules with a left side of 5 nodes such as
`sub(x, sub(0, y)) -> add(x, y)` and `sub(x, add(x, y)) -> sub(0, y)`, which are neither instances of the first 20 rules nor reachable by blind sampling (a random draw of that size hits a specific rule with
probability far below 1 in 12768). The miner's value-signature index is what concentrates its proposals on true, relevant rules: 48% of its candidates are provable against 4.2% of random ones, and its 32
provable candidates cover 36 stragglers against 535 for 3. So the floor is low: a proposer needs execution feedback (the straggler's own subterms and values) to compete with the miner, and rule transfer from
other families helps with only the trivial identities. Caveats: one seed and one target family; the random proposer's cost (about 277 s per scoring round for 535 provable candidates) means a larger sample was not tried;
the pilot proposers skip the miner's applicability prefilter on purpose. Not done: a model proposer (P5), which needs your go-ahead for either a subagent or an outside call.

## 67. Proposer benchmark: the enumerator's reach, and the `file` proposer (2026-10-02)

**Harness.** `RULEMINER_PROPOSER=file` reads rules from `RULEMINER_PROPOSER_FILE` (one `lhs -> rhs` per line in `Term::show` syntax, `#` comments), through `parse_term`, into the same rule-order
check, `prove_rule` and cumulative scoring as every other proposer. Demo file of three rules and one non-rule: the false rule `add(x, y) -> xor(x, y)` was refused, the two true rules were chosen and fixed 14 of the 79 stragglers.

**Reach of the enumerator (is there headroom for a proposer on bigger terms?).** `RULEMINER_SIZE` is the node count of the pool the miner indexes by value (the right sides it can propose); same target as section 66
(shr, `ABLATE=promoted`, 79 stragglers, 8 scoring threads, release, BelowNormal, CPU 30-94% from other sessions, Defender RTP off, one run each):

| Pool size | Terms | Distinct functions | Oriented candidates | Provable | Candidate generation | Covered | Chosen rules |
|---|---|---|---|---|---|---|---|
| 5 (default) | 5804 | 617 | 67 | 32 | 0.3 s | 36 of 79 | 17 |
| 6 | 44332 | 2950 | 75 | 32 | 1.5 s | 36 of 79 | identical |
| 7 | 415788 | 13660 | 87 | 32 | 12.1 s | 36 of 79 | identical |

The pool grows about 7.6x per size (size 8 would be about 3 million terms, size 9 about 25 million), so a proposer could in principle reach where enumeration cannot, but **on this target there is nothing beyond size 5 to find**: the 32 provable
candidates and the chosen rules are the same at sizes 5, 6 and 7 (same hash of the `chosen` lines), and the other 43 stragglers are not coverable by a two-variable rule of up to 7 nodes. So these stragglers give a proposer no headroom; a benchmark with
headroom needs harder laws (a depth-3 law pool, or three variables; both are fixed to 2 in the miner) and is not built.


## 68. A benchmark with headroom (`add3`) and a rule corpus (2026-10-02)

**Benchmark.** `RULEMINER_FAMILY=add3`: laws over `x`, `y`, `z` from the pool `add3_pool()` (depth-1 terms over three variables and the constants, plus one sum or difference of a depth-1 term and a leaf), equal on all 4096 width-4 inputs, plausible at widths 1-6, using all three variables.
35 laws proved by `rewrite_law` at width 4 under the built-in rules, **12 stragglers** (each needs one whole-term machine proof; all reassociation or permutation laws of `add`/`sub`). (First measured as 21 of 77; that count came from the `contains` bug below, which let `xor` laws through the "uses all three variables" filter. Corrected in section 69.)

| Proposer | Covered of 12 |
|---|---|
| none | 0 |
| the miner (cross-side candidates, `RULEMINER_VARS` 4) | 6, by one rule: `sub(add(x, y), z) -> add(sub(x, z), y)` |
| `file`: two hand-written rules (`add(sub(x,y),z) -> sub(add(x,z),y)`, `sub(sub(x,y),z) -> sub(x, add(y,z))`) | **12** (9 + 3) |

So the headroom is 6 laws that a proposer can fix and the miner does not. (My first reading, that all of them are beyond the miner, was wrong: a one-rule check of the miner showed it covers some.)

**The rule order refuses these rules.** `rule_order_ok` is a weight order; reassociation, permutation and `xor(_, -1)`-for-`sub` rules tie in it (same weight, same variable occurrences), so with the default order the hand rules were "0 decreasing" and none was tried. `RULEMINER_LOOSE=1` (a stopgap, replaced by `RULEMINER_PERM=1` in section 70) let a non-`mined` proposer skip the order check (the step budget and the same-term check in `rule_step` still bound the rewriter; the kernel decides soundness, not the order).

**Latent bug fixed.** Several variable-set checks used `t.show().contains(VARS[v])`, which matches `xor` for `x` and `sub` for `u`. They were prefilters (candidate selection in the `transfer` proposer and the cross-side generator, and the admission meta-test's pair filter), so nothing unsound was accepted, but the sets were wrong. All now use `Term::has_var`. The suite passes; the section 64-67 numbers were not rerun, and the effect should be small (a prefilter that only dropped candidates that could not be rules), but the `add3` family count changed from 21 of 77 to 12 of 35 (see above).

**Corpus.** `mint_corpus` (ignored test, `CORPUS_OUT=<file>`) writes true rules in the `file:` syntax: two-variable depth-2 pool plus the `add3` pool, grouped by value on all width-4 inputs, left side larger than right, at least two distinct variables on the left, no all-constant operator node on the left (constant folding is trivial), up to 6 right sides per left, each plausible at widths 1-6 and proved and kernel-checked at widths 3 and 4. Run: **1810 rules, 1810 proved** (436 use `z`), 63 s, CPU 33-40%, Defender RTP off. Neither hand rule is in it (checked by exact line), but 216 lines have nested `add`/`sub`, so a model trained on it may be near the benchmark's rules; to measure generalisation, hold out by left-side shape, not by line. Right sides are not canonical (`and(-1, x)` appears for `x`; up to 6 equal right sides per left), which a model would have to be trained around. The corpus file is not committed; it is regenerated in about a minute.

**Open.** A model proposer's training split and its held-out evaluation (the 12 stragglers plus the 2-rule answer key) are defined but nothing is trained.

## 69. Goal-as-lemma baseline on `add3` (2026-10-02)

`RULEMINER_PROPOSER=goal` proposes each straggler's normalized sides as a rule, both directions (24 proposals for 12 stragglers; `RULEMINER_LOOSE=1`), and the usual cumulative scoring picks. It is a heuristic with no learning, the baseline a model proposer has to beat.

| Proposer on `add3` (12 stragglers) | Covered | Rules chosen |
|---|---|---|
| miner | 6 | 1 |
| `goal` | 9 | 1 (`add(sub(x, y), z) -> sub(add(x, z), y)`) |
| `file` (two hand rules) | 12 | 2 |

`goal` beats the miner by 3 and misses the 3 permutation laws `sub(sub(a, b), c) = sub(sub(a, c), b)`: as a rule that law maps a term to a variable permutation of itself, so it can never fire usefully (the step guard skips a rewrite that returns the same term, and the budget stops a loop), and no proposed form of it is decreasing. The hand rule that fixes them, `sub(sub(x,y),z) -> sub(x, add(y,z))`, is not a goal restated; it needs a normal form the stragglers do not contain. So the remaining headroom (3 laws) needs a proposer that invents a normal form, not one that restates goals. CPU 34-52% during the runs, Defender RTP off, one run each.

## 70. Tie-break for the rule order, rerun of sections 64-67, a deeper `add3` benchmark (2026-10-02)

**Tie-break (`RULEMINER_PERM=1`, replaces `RULEMINER_LOOSE`).** `rule_order_ok` rejects rules of equal weight and equal variable occurrences. `rule_order_or_tie` breaks such ties by `tie_greater` on the patterns: head precedence (`add` > `sub` > `xor` > `and` > `or` > `lt` > shifts), and for equal heads the first differing operand pair (left to right) by size, then recursively. It orients `sub(sub(x, y), z) -> sub(x, add(y, z))` and `add(sub(x, y), z) -> sub(add(x, z), y)` (one direction each; a unit test checks both ways) and not commutativity. It is a tie-break, not a termination proof: `RULE_BUDGET` and the same-term check remain. On `add3`: the two hand rules are admitted (2 of 2 decreasing) and cover 12 of 12 as before; `goal` has 6 of 24 proposals decreasing (was 24 under LOOSE) and the same 9 covered; the miner is unchanged at 6.

**Rerun of the section 66-67 numbers after the `has_var` fix** (shr, `ABLATE=promoted DEEP=1 MINER_SUB=1 STRIDE=3 LAWS=900 ANY=1`, 8 threads, BelowNormal, CPU 40-55%, RTP off): 79 stragglers; miner **36 of 79** with `RULEMINER_ROUNDS=30` (32 provable of 67; **27 of 79 with the default 8 rounds**, so state the round count with any coverage number); `transfer` 3 of 79 (122 of 153 provable). Unchanged from sections 66-67.

**Deeper `add3`** (`RULEMINER_DEEP3=1`, the pool plus sums and differences of two depth-1 `add`/`sub`/`xor` terms; `RULEMINER_LAWS=150 STRIDE=7`; `PERM=1`; 8 threads, 8 rounds):

| | Stragglers | Covered | Rules chosen |
|---|---|---|---|
| none | 64 of 150 laws | 0 | |
| miner | | **41** (23 uncovered) | 8 |
| `goal` (128 proposed, 46 decreasing) | | 26 | 8 |

Scoring was the slow part (miner run 742 s, `goal` 600 s; the first attempt with `LAWS=400` and one thread ran over 25 minutes and was killed). So here the miner beats the goal-as-lemma baseline, the opposite of the shallow `add3` result (9 vs 6), and 23 stragglers are left. **There is no answer key for those 23**, and nothing says they are coverable by short rules; a proposer's score on them is a lower bound on what exists. An answer key (hand rules, kernel-proved) is the missing piece for a fair model evaluation.

## 71. Answer key for the deep `add3` stragglers, and faster scoring (2026-10-03)

**Answer-key attempt.** Eight hand-written rules (the miner's chosen ones plus `sub(x, sub(y, z)) -> add(sub(x, y), z)`, `add(x, sub(y, -1)) -> sub(add(x, y), -1)`, `sub(x, xor(y, -1)) -> sub(add(x, y), -1)`, `xor(-1, x) -> xor(x, -1)`, `sub(sub(x, y), z) -> sub(x, add(y, z))`), all provable, admitted with `RULEMINER_PERM=2` (no order check; the miner's own cross-side rules are not ordered either), cover **42 of 64**, against the miner's 41. The 22 left over are all abelian-group identities in `add`, `sub`, `0`, `-1` and `xor(_, -1)` (= `-1 - _`), for example `add(y, z) = add(sub(z, x), add(x, y))` and `add(sub(x, z), y) = add(sub(y, z), x)`. Closing them needs associativity and commutativity of `add` as a normal form (a linear form `sum of c_i x_i + k`), which oriented rules cannot express; more rules loop or tie. **So there is no rule-shaped answer key for them, and a rule proposer, model or not, cannot be scored on them.** A model proposer evaluated on this family would be measuring something the rule format cannot reach. The route to those laws is an AC normalizer in the rewriter (flatten `add`/`sub`/`xor(_, -1)` chains, sort, cancel), whose per-step proofs are `add` associativity and commutativity instances; not built.

**Scoring time.** The deep miner run (742 s) is dominated by tail candidates, not by machine proofs: per candidate about 1.2 s single-threaded, but a candidate that interacts with a chosen rule (`add(x, sub(y, z)) -> add(sub(x, z), y)` next to `add(sub(x, y), z) -> sub(add(x, z), y)`) took 21 s because each of the 64 stragglers burns the whole 200-step budget, and a round waits for the slowest worker. Two switches, both leaving the chosen rules and coverage identical in every run checked:
- `RULEMINER_STEPS` (default 200): per-straggler rule-step budget while scoring. At 40: rounds 30 s -> 6-15 s on the key file.
- `RULEMINER_FAST=1`: `prove_eq`'s machine fallback is counted without building its proof (placeholder `var(0)`, never checked; `SCORE_ONLY`). About 26% on the key file alone. **Not exact in general (section 72): off by default.**
- `RULEMINER_TRACE=1` prints per-candidate scoring times.

| Run (deep `add3`, 8 threads) | Before | `STEPS=40`, `FAST=1` | Chosen rules / coverage |
|---|---|---|---|
| miner | 742 s | **322 s** | identical (41 of 64) |
| key file | 275 s | 107 s | identical (42 of 64) |

Not checked: `STEPS=40` on the `shr` run (79 stragglers, 36 covered); the default stays 200. CPU 40-65% from other sessions, RTP off.

## 72. Speed-ups checked on `shr`; a sub-normal-form attempt on deep `add3` (2026-10-03)

**`shr` (79 stragglers, `ABLATE=promoted DEEP=1 MINER_SUB=1 STRIDE=3 LAWS=900 ANY=1 ROUNDS=30`, 8 threads; CPU 55-60% from other sessions, RTP off).** Baseline: 36 of 79, 19 rules chosen.
- `RULEMINER_STEPS=40` alone: **identical** chosen rules and coverage (312 s, against 462 s for the baseline run, which was under heavier load).
- `RULEMINER_FAST=1` (with or without `STEPS=40`): **34 of 79**, different late rules (198 s). Cause: in `rewrite_law`, when the whole-term machine proof fails (`add_tree_law` returns `None`), the code falls back to `shr_mask_eq`, which can succeed without a machine proof; the placeholder returned by `FAST` skips that path, so some stragglers count as not fixed. `FAST` is exact only where the fallback cannot fail (identical on `add3`, three runs). It stays off by default and should not be used on `shr`.
- `STEPS=40` is exact on `shr` (one run) and `add3` (three runs); the default stays 200.

**Sub normal form on deep `add3`.** The rewriter already normalizes `add` chains (associativity, commutativity, `0`, `a + ~a`) but treats `sub(a, b)` as an atom, so `add(sub(x, z), y)` and `add(sub(y, z), x)` stay different. I tried the obvious fix as `file` rules (17: pull `sub` outward, `add(sub(x, y), z) -> sub(add(x, z), y)`, `add(x, sub(y, z)) -> sub(add(x, y), z)`, `sub(x, sub(y, z)) -> sub(add(x, z), y)`, `sub(sub(x, y), z) -> sub(x, add(y, z))`, four cancellation variants `sub(add(x, z), add(y, z)) -> sub(x, y)`, `sub(add(x, y), x) -> y`, `add(sub(x, y), y) -> x`, `xor(x, -1) <-> sub(-1, x)`, ...): **40 of 64** (the 8-rule key of section 71 gets 42). Scoring is per rule and per straggler: a cancellation rule alone fixes nothing until the sums are in normal form, so the greedy scorer never picks it and the file proposer's loop does not combine rules. The 22 leftovers need the normal form and the cancellation applied together, i.e. a normalizer, not a rule. Negative result; nothing kept besides the numbers.

## 73. New family `mix3`, permutative rules, bundles (2026-10-03)

**Probe for a family with rule-shaped headroom.** `RULEMINER_FAMILY=mix3`: depth-1 terms over `x`, `y`, `z`, `0`, `-1` with all of `add`, `and`, `or`, `xor`, `sub`, `shl1`; then each operator over a depth-1 term and a leaf (both orders), `shl1` of a depth-1 term, and sums of two depth-1 terms (`mix3_pool`); laws equal on all 4096 width-4 inputs and using all three variables. Run: `STEPS=40`, `PERM=1`, 8 threads, 8 rounds, CPU 30-60%, RTP off.

| Sample | Laws | Stragglers | Miner covers | Left |
|---|---|---|---|---|
| every 9th, 150 laws | 150 | 8 | 5 | 3 |
| first 1500 laws | 1500 | 174 | 122 (7 rules, 626 s) | **52** |

The 52 are the same class as the deep `add3` leftovers: `add(sub(x, y), z) = add(sub(z, y), <x written another way>)`, where the other way is `and(x, x)`, `or(x, 0)`, `xor(0, x)` and so on (24 of the 52 involve `and`/`or`), i.e. an `add`/`sub` association law with a bitwise identity inside. So the bit-trick mixes add no new kind of straggler: the machinery already closes them, and what is left is `sub` as an atom inside `add` chains.

**Permutative rules.** `rule_permutative(l, r)`: tied in the rule order and not oriented by `tie_greater` either way (`add(sub(x, y), z) -> add(sub(z, y), x)`). `rule_step` applies one only when the instance's right side is smaller than the term by `show()` (ordered rewriting, a total order on instances, so no rule undoes itself); `RULEMINER_PERM=1` admits them. Unit test added. `RULEMINER_BUNDLE=1` additionally scores all provable candidates added together, since the greedy scorer rates a rule by what it fixes alone and a rule that only works with others scores 0.

**Result on deep `add3` (64 stragglers).**

| Rule set (all hand-written, all provable) | Covered |
|---|---|
| 8-rule key of section 71, greedy | 42 |
| + permutative rules, bundle of 8 | 40 (permutative rules alone add nothing) |
| + cancellation variants, three-term chains, pulling `sub` outward (24 rules), bundle | **44** |

The 20 left all involve the constant `-1`: `sub(z, -1)` (z + 1), `xor(z, -1)` (= -1 - z, the builtin normal form for `sub(-1, z)`, so my `xor -> sub` rules fight it) and sums of such terms. Closing them needs the rewriter's constant handling (`sub(x, -1)` as `x + 1`, `1` being `sub(0, -1)`), which has no rule form that does not loop with the zero and `xor` rules; not built. Negative-to-partial result: rules plus ordered rewriting go from 41 (miner) to 44 of 64; the last 20 are a constants problem, not an AC problem.

## 74. Base rules plus the miner; where the last 7 stand (2026-10-03)

**`mix3` with the 24-rule bundle of section 73** (`file` proposer, `BUNDLE=1`, `PERM=2`): **150 of 174** stragglers covered (the miner alone: 122). The 24 left all contain `xor(_, -1)`, the same constants problem as deep `add3`.

**`RULEMINER_BASE=<file>`** puts a rule file in force throughout (stragglers are those left with it; scoring adds the miner's candidates on top; a step budget bounds the straggler phase when a base is present, since hand rules can loop). `scripts/data/add3_base_rules.txt` is the 22-rule base (the 24 of section 73 minus the two `xor -> sub` rules, which duplicate the builtin `notsub` and made the rewriter loop; stack overflow before the fix).

Deep `add3`, base of 22 rules, then the miner (`PERM=1`, `STEPS=40`, `FAST=1`, 8 threads, 8 rounds, CPU 30-60%, RTP off): 20 stragglers left by the base, **the miner closes 13 with 3 rules**, so **57 of 64** overall (miner alone 41, hand rules alone 44):

| Mined rule | Fixes |
|---|---|
| `add(x, xor(y, -1)) -> add(-1, sub(x, y))` | 9 |
| `sub(add(xor(x, -1), y), z) -> sub(add(xor(z, -1), y), x)` | 3 |
| `sub(x, add(y, add(x, z))) -> sub(0, add(y, z))` | 1 |

The first is the missing constants rule of section 73 (`x + ~y = x - y - 1`), found by the existing miner once the `sub` normal form was in the base. So the division of labour works: hand rules give the normal form, the miner finds the constant-handling rules.

**The last 7** (`add(sub(x, y), sub(z, -1)) = sub(sub(x, y), xor(-1, z))` and its permutations, `add(xor(y, -1), sub(x, z)) = add(sub(x, y), xor(-1, z))`): bisecting the rule set shows `sub(sub(x, y), z) -> sub(x, add(y, z))` blocks one of them (removing it makes both sides meet). The rules disagree on the shape of `sub(sub(a, y), sub(-1, z))` (reassociate first, or pull the inner `sub` out first), so the set is not confluent on terms mixing nested `sub` with `-1`. A confluent set needs completion (Knuth-Bendix style) or a real linear-form normalizer; not attempted.

`normal_forms` (ignored test, `NF_LAWS`, `NF_RULES`) prints both sides' normal forms under the built-in rules plus a rule file; it is how the clash was found.

## 75. The clash was `subdist`; both families closed (2026-10-03)

**Cause of the last 7 (section 74).** Not non-confluence of my rules but a 4-cycle with the builtin rule `subdist` (`sub(add(x, y), add(z, u)) -> add(sub(x, z), sub(y, u))`, mined in section 37): my pull-out rules (`add(sub(x, y), z) -> sub(add(x, z), y)`, ...) build `sub(add(..), add(..))`, `subdist` splits it again, and the loop burns the step budget, leaving the term half-normalized. Found with `NF_TRACE=1 normal_forms` (prints every rule application). The two normal forms are alternatives: the builtins distribute `sub` over sums, the base pulls it out. With `ABLATE=subdist` all 7 meet.

**Results with the base of 22 rules (`scripts/data/add3_base_rules.txt`) and `ABLATE=subdist`**, then the miner (`PERM=1`, `STEPS=40`, 8 threads, 8 rounds, CPU 30-60%, RTP off):

| Family | Laws | Stragglers left by the base | Mined rules | Covered | Overall |
|---|---|---|---|---|---|
| deep `add3` (`DEEP3=1 LAWS=150 STRIDE=7`) | 150 | 20 (of 64 for the builtins alone) | 3 | **20 of 20** | 64 of 64 |
| `mix3` (first 1500) | 1500 | 24 (of 174) | 1 | **24 of 24** | 174 of 174 |

Mined rules: `add(xor(x, -1), y) -> add(-1, sub(y, x))` (does 16 of the 20 on `add3`, all 24 on `mix3`), `add(x, xor(y, -1)) -> add(-1, sub(x, y))`, `sub(x, add(y, add(x, z))) -> sub(0, add(y, z))`. Final rule files: `scripts/data/add3_final_rules.txt` (25 rules), `scripts/data/mix3_final_rules.txt` (23 rules). (Earlier, without the ablation, the same base left 7 on `add3` and 3 on `mix3`.)

**Kernel check** (`rule_set_kernel_check`, ignored test: every law `rewrite_law` proves under builtins less `ABLATE` plus a rule file is checked at width 4): deep `add3`, 150 laws, **150 checked, 150 with no whole-term machine proof**, 0 unproved. `mix3`, 1500 laws, **1500 checked, 1464 without a whole-term machine proof** (36 still use at least one: "covered" means fewer machine proofs than the builtin baseline, not none), 0 unproved. Width 4 only; the rules are proved per width on use, and the section 65 scaling sweep was not rerun with this rule set.

**What this changes.** Both bit-trick and add/sub families are now closed by 22 hand-written rules plus 1-3 mined rules, with `subdist` ablated. The earlier conclusion "no rule-shaped answer key exists" (section 71) was wrong for deep `add3`: the key is the base plus the three mined rules, and it was missing a `subdist` ablation, not an AC normalizer. The two conventions (`subdist` on or off) are not both usable at once; promoting the 25 rules as builtins would need `subdist` removed from `rules()` and the 15 other families' results rechecked (not done).

## 76. `subdist` kept builtin; final rule sets scaled to n=64 (2026-10-03)

**`subdist` removal** (quick comparison, width 4, miner stragglers; the `shr` settings were passed from memory and not verified against section 65): default builtins vs `ABLATE=subdist` vs `ABLATE=subdist` plus `key5.txt` (an add3 rule file kept in `$TEMP`).
mul 2 / 9 / 1 (base time 1.6 s vs 28.4 s without `subdist`), shl 5 / 5 / 5, lt 28 / 28 / 28, shr 43 / 43 / 38. Removing `subdist` hurts mul, so it stays builtin and `add3` / `mix3` opt out with `ABLATE=subdist`; promoting the 25- and 23-rule sets as builtins needs a non-cycling replacement first.

**Scaling** (`scaling_sweep` now takes `SWEEP_RULES=<file>` and `SWEEP_FAMILY=add3|mix3`; per-law rule budget 200; `ABLATE=subdist`; release, BelowNormal; CPU 48-75% from other sessions, RTP off; one run each). 20 evenly spaced laws of the deep pools, rewrite + kernel check, seconds (build + check):

| Family | n=4 | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|---|
| add3 + `add3_final_rules.txt` | 4.4 | 3.4 | 7.0 | 24.0 | 112.7 |
| mix3 + `mix3_final_rules.txt` | 3.2 | 2.5 | 4.8 | 11.3 | 49.0 |

All 20 laws proved and kernel-checked at every width, 0 unproved, exactly 1 whole-term machine proof per width (the same law each time, so it is one of the 36 laws that still use one). Growth is about 2x per doubling up to n=32, then 4.7x (add3) and 4.3x (mix3) at n=64, where the slowest law (`add(add(x,y),xor(z,-1))`) alone costs 29 s: load noise is possible (CPU up to 75%) but the jump is in both families, so treat superlinear growth at n=64 as plausible. Not measured: n=128, other sample sizes, a quiet machine.

## 77. Transfer between pools; reversing `subdist` (2026-10-03)

All runs: `RULEMINER_PERM=1 STEPS=40 THREADS=8 ROUNDS=8`, release, BelowNormal, CPU 40-75% from other sessions, RTP off, one run each; `ABLATE=subdist` unless noted. Stragglers are those left under the named rule file.

**Transfer** (rules mined on one pool, stragglers counted on the other; the pools share operators and variables, so this is a weak held-out test):
| Pool | base 22 rules | other pool's final set | own final set |
|---|---|---|---|
| mix3 (1500 laws) | 24 | **0** (`add3_final`) | 36 with `mix3_final` alone (a miner pass then covers the rest) |
| deep add3 (150 laws, stride 7) | 20 | **4** (`mix3_final`) | 0 (`add3_final`, section 70) |

The 3 rules mined on `add3` close every straggler of `mix3` without any mixing. The one rule mined on `mix3` closes 16 of the 20 `add3` stragglers. The mined rules are not tuned to one pool.
(Note: `mix3_final` alone leaves 36 stragglers, more than `add3_final` does; the 36 are the laws section 75 counts as "still use a machine proof".)

**Reversed `subdist`** (`add(sub(x, z), sub(y, u)) -> sub(add(x, y), add(z, u))`, the direction the tie-break order picks, as a rule file with builtin `subdist` ablated): mul 5 stragglers (builtin 2, ablated 9; base time 5.8 s vs 1.4 s vs 33 s), shl 5, lt 28, deep add3 with `add3_final` 0, mix3 with `mix3_final` 36 (same as without it). It never clashes with the rule sets, but it recovers only part of what the forward `subdist` gives mul. A `shr` row was run without the section 65 settings (65 laws, 1 straggler) and is not comparable. So no clean replacement yet; `subdist` stays builtin, the rule sets keep `ABLATE=subdist`.

## 78. Rule-LM pilot setup: corpus, split, Burn smoke test (2026-10-03)

**Route** (chosen by the user): Burn on the Vulkan backend (wgpu/cubecl), CPU first only if a run proves GPU-unfriendly; a separate crate `tools/rulelm/` (own `[workspace]`, own `target`) so the kernel crate gains no dependencies. Model: a language model over corpus lines `lhs -> rhs`, usable unconditionally (sample from nothing) and conditionally (prompt with a left side, e.g. the abstracted subterms of a straggler as the `goal` proposer builds them).

**Corpus.** `CORPUS_MAX` does nothing at the default `CORPUS_PER_LEFT=6`: the pools hold only 1810 candidates. `CORPUS_PER_LEFT=1000` gives 2962 candidates, all proved and kernel-checked at widths 3 and 4 (62 s). Only 3 of the 22 base rules (and 3 of the 25 `add3_final`) are in the corpus: the base rules are deeper than the corpus pools, so they are held out by construction. A bigger corpus must therefore come from symmetry, not a deeper pool.

**Symmetry and split** (`scripts/corpus_augment.py`): the family of a rule is every renaming of `x, y, z` and every swap of `add`/`and`/`or`/`xor` operands. Families containing any of the 25 held-out rules (22 base + the mined ones) are removed from training (24 corpus-side rules; the held-out set has 414 variants). Result: `scripts/data/rulelm/train.txt` 7218 rules from 2962; spot check of 2000 variants at width 4, 20 random inputs each: 0 violations. Held-out test: `heldout_rules.txt` (25 rules) and its variants.

**Burn smoke test** (`tools/rulelm`, `burn =0.22.0-pre.4`, features `wgpu vulkan autodiff std`; it pulls `cubecl 0.11.0-pre.4`, the version scratchtape pins): builds in under ten minutes from a cold cache. `Device::vulkan(DeviceKind::DiscreteGpu(0)).autodiff()`; a 1024x1024 matmul + backward runs in 3-6 ms after a 1.25 s first step; 6000 steps ran with the process listed on the RX 9060 XT's LUID (so `DiscreteGpu(0)` is the eGPU) alongside another session's game client (a shared GPU; timings are not clean). Defender RTP off, CPU about 20% at launch.
Burn 0.22 has no backend type parameter: tensors are `Tensor<const D>` and the device chooses the backend (`Device::autodiff()`, `into_scalar::<f32>()`).

## 79. Rule-LM pilot, first results: negative (2026-10-03)

**Model** (`tools/rulelm`, Burn 0.22 pre.4 on the RX 9060 XT via Vulkan): character-level causal transformer, 4 layers, d=128, 4 heads, feed-forward 512, dropout 0.1, pre-norm; lines are `
 lhs -> rhs 
` padded to 50 tokens; Adam, learning rate 1e-3 with a 200-step warm-up and linear decay, batch 128, 3000 steps (284 s, about 0.1 s/step, GPU shared with another session's game client). Data: `scripts/data/rulelm/train.txt` (7218 rules; 5% of it is a monitor split, not independent because renamed copies are in both parts). `rulelm sample CKPT N TEMP SEED [PREFIX]` samples; a first version had no start token and sampled garbage (position off by one, first character untrained); fixed with the leading newline.
Loss per character: monitor 0.30; held-out variants 1.49 after 200 steps, rising to 2.43 at 3000 (an 8000-step run before the start-token fix: 1.35 to 3.2). The model fits the training distribution and does worse on the held-out rules the longer it trains.

**Harness.** `scripts/filter_candidates.py` keeps sampled rules true at widths 3-6, with a smaller right side. The `file` proposer of `rule_miner` now gets the same applicability prefilter and cap as `mined` (a left side must match a subterm of a straggler's normalized terms); without it, 4409 candidates ran over 40 minutes and were killed (for about a minute that overlapped another run, 16 threads against the 12 cap).

**Results** (deep `add3`, `PERM=1 STEPS=40 ROUNDS=8 DEEP3=1 LAWS=150 STRIDE=7`, 64 stragglers; CPU 25-95% from other sessions, RTP off, one run each):
| Proposer | Candidates | Stragglers covered |
|---|---|---|
| `mined` (the miner, 59 applicable left sides) | 59 | **51 of 64** |
| model, unconditional: 8000 samples (T 0.7 and 1.0), 4752 distinct, 4409 true and smaller | 4409 | **0** (0 applicable to a straggler) |
| model, conditional: the 59 miner left sides as prompts, 100 samples each at T 0.8 | 272 distinct | **0** (none true) |

4404 of the 4409 true unconditional samples are rules from the training set; **none of the 414 held-out variants** appears among the unconditional or conditional samples.
**Why, in part by construction:** training lines are at most 32 characters, 390 of the 414 held-out variants are longer, and so are the miner's left sides (median 25 characters plus the right side). The model never saw positions beyond 33, so it cannot write the rules we ask for. The negative result therefore says "a model trained on shallow rules does not extrapolate to deep ones", not "a model cannot do this". The fair test needs training data of the same depth: mint from the deep `add3` and `mix3` pools with every family of the 25 held-out rules removed (neighbours of held-out rules will still be in training, so the split is only family-level).

## 80. Rule-LM on a deep corpus: still far below the miner (2026-10-03)

**Corpus.** `mint_corpus` gained `CORPUS_DEEP=1` (adds the deep `add3` and `mix3` pools) and `CORPUS_CHARS` (longest line kept). `CORPUS_DEEP=1 CORPUS_CHARS=46 CORPUS_PER_LEFT=4`: 42174 candidates; the first attempt at `CORPUS_MAX=40000` ran 31 minutes with 11.5 GB resident and printed nothing (the file is written at the end), so it was killed; `CORPUS_MAX=6000` (every seventh) took 9.5 minutes: 4174 kept of 6000 tried (width-3/4 proofs and kernel checks). Merged with the shallow corpus: 6925 rules; `corpus_augment.py` with the 25 held-out rules (414 variants) removed: **38784 training rules**, median length 43, max 46, 29904 over 32 characters, none a held-out variant (`scripts/data/rulelm/train_deep.txt`, `corpus_deep.txt`).
**Training:** same model, 6000 steps, 700 s. Loss per character: monitor 0.27; held-out variants 0.94 at step 200, rising to 1.21 at 6000 (shallow corpus: 1.49 rising to 2.43), so the deep data helps, and overfitting to the training distribution still grows with steps (the saved checkpoint is the last one).
**Samples:** unconditional 8000 (T 0.8, 1.0): 6694 distinct true and smaller rules, **6564 of them in the training set** (98%), 2 held-out variants (`sub(add(y, x), x) -> y`, `sub(add(z, y), z) -> y`). Conditional (the 59 miner left sides, 100 samples each, T 0.8): 680 distinct, 32 true, all 32 in training, 0 held-out.
**Coverage** (deep `add3`, same settings as section 79, 64 stragglers): `mined` 51 of 64; model candidates (6723 true, after the applicability filter 47, all provable): **8 of 64**, with rules like `add(sub(x, y), add(y, z)) -> add(0, add(x, z))` (the miner's size score rewards removing `sub`; the rule is true and does help a little). The base rule `add(sub(x, y), z) -> sub(add(x, z), y)` and its relatives were never proposed.
Reading: with matching depth the model moved from 0 to 8 of 64, mostly by recombining training rules; it does not propose the reassociation rules that close the family. Single runs; CPU 30-90% from other sessions.

## 81. Rule-LM variants: early stopping, small model, token-per-operator (2026-10-03)

`rulelm` takes `RULELM_WORDS=1` (one token per operator or leaf; rules in prefix notation, `scripts/rule_notation.py`, data `train_deep_prefix.txt`, `heldout_variants_prefix.txt`, at most 13 words), `RULELM_D`, `RULELM_LAYERS`, `RULELM_DROPOUT`, `RULELM_EVERY`, `RULELM_SAVE_BEST` (keep the checkpoint with the lowest held-out loss). Same deep corpus, harness and 64 stragglers as section 80; one run each; CPU 25-90% from other sessions, RTP off.

| Model | Checkpoint | True and smaller (unconditional / conditional) | Applicable | Stragglers covered |
|---|---|---|---|---|
| char, default (section 80) | step 6000 (last) | 6694 / 32 | 47 | 8 |
| A: char, default | best held-out (step 100, loss 0.885) | 30 / 4 | 5 | 4 |
| B: char, d=64, 2 layers, dropout 0.3 | best held-out (early) | 50 / 11 | 11 | 6 |
| B2: same as B | step 3000 (last) | 371 (234 in training) / 23 | 23 | 8 |
| C: words, default | best held-out (early) | 1506 / 0 | 0 | 0 |
| C2: words, default | step 3000 (last) | 6661 (6512 in training, 2 held-out hits) / 0 | 31 | 8 |
| union of all proposals above (13625 true rules) | | | 75 | **8** |
Miner (`mined`): 51 of 64.

Findings. (1) **Held-out loss is not a usable stopping criterion**: its minimum sits at step 100-200, where the model has not yet learned the syntax (A's samples are mostly malformed: 30 true of 6998), so "best held-out" checkpoints do worse than the last one. (2) A smaller, more regularized model (B2) writes fewer valid rules but ends at the same 8. (3) The word-level encoding (C2) writes valid rules reliably (6661 true) but conditionally none (0 of the 59 prompts), and reaches 8 too. (4) Every variant, and their union, caps at the same 8 stragglers, via the same six rules (`add(sub(x, y), add(y, z)) -> add(0, add(x, z))` and relatives), none of them a held-out family; 98% of the true proposals are training rules. The rules that close the family (reassociation, `add(sub(x, y), z) -> sub(add(x, z), y)`) are never proposed. So the ceiling here is the training distribution, not model size, token granularity or stopping point.


## 82. Scaling of the other families, and n=128

`scaling_sweep` with the built-in rules only, 40 laws per family (evenly spaced among the true laws), kernel-checked at every width (`scripts/experiments/sw2.sh`; logs `sw2_*.out`, `s128_*.out`). Seconds (build / check), machine proofs per width:

| Family | n=4 | n=8 | n=16 | n=32 | n=64 | n=128 (20 laws) | machine proofs |
|---|---|---|---|---|---|---|---|
| mul | 20.9 / 1.7 | 1.6 / 2.6 | 4.0 / 4.4 | 7.1 / 14.5 | 16.1 / 37.0 | 30.6 / 73.2 | 0 |
| shl | 0.4 / 0.2 | 0.4 / 0.2 | 1.0 / 0.6 | 1.8 / 1.6 | 3.8 / 4.5 | 2.5 / 3.0 (10 laws) | 1 (0 at 128) |
| lt | 0.5 / 0.4 | 1.1 / 0.8 | 2.1 / 2.1 | 3.7 / 5.0 | 12.9 / 20.2 | 22.3 / 33.2 | 3 |
| shr | 0.5 / 0.2 | 0.8 / 0.3 | 1.9 / 0.6 | 2.1 / 1.2 | 5.7 / 3.5 | 4.7 / 7.0 | 1 (0 at 128) |

All 40 of 40 (20 of 20, 10 of 10 at 128) proved and checked at every width. The n=4 mul build time is the one-off 18.7 s for `(7*7)x = 7(7x)` (memo warm-up); later widths reuse the memoized rule laws. Check time grows about 2.5x per doubling for mul and lt, about 2x for shl and shr: polynomial, no cliff. The machine-proof count is constant in n (a fixed set of straggler laws per family).

n=128 first failed with a kernel type mismatch on `shl1(-1, 0) = ...`: `Term::Ones` and several masks were built as `(1u128 << n) - 1`, which wraps to 0 at n=128 in release. Fixed with a `low_bits(n)` helper in six places in the term pipeline; four test-only masks (lines near 206, 1026, 1126, 1320) still use the old form but run at small n. The shl sample at 128 is smaller (10) because it was the probe; it was not rerun at 20.

Load: the machine was busy during the runs (CPU 32-86% at start and end of each sweep, from other sessions), Defender RTP off, so times are upper bounds; the 128-bit runs were at BelowNormal.

## 83. Design: lemma midpoints (not built)

Problem. After §80-81 the miner closes 51 of 64 deep-add3 stragglers and the rule LM 8. A straggler is a law `t1 = t2` whose normal forms `n1 ≠ n2` (stuck under the current rules, equal as functions) still need a whole-term machine proof. The goal proposer (§36 line) abstracts subterms of `n1`, `n2` into patterns and looks for a smaller equal term; it fails on the remaining 13, plausibly because the equality needs an intermediate term that is not smaller than either side (reassociation passes through an expanded form).

Idea. Find `m` with `n1 =>* m` and `n2 =>* m`, where `=>` is one instance of a known-true law in either direction (the oriented rules, their reverses, `rule_permutative` swaps), then promote the *halves* `n1 = m` and `m = n2`, abstracted by the goal proposer, instead of `n1 = n2`. Each half is a shorter, more local equality and may generalize where the whole does not. A found path is also a machine-free proof of the straggler in its own right (every step is a proven rule instance), so no new trusted code is needed; only candidates are generated, the kernel still checks.

Search for `m`. Bidirectional breadth-first search from `n1` and `n2` over single steps (all rules both ways, applied at any subterm), memoized on `show()`, depth cap `d` per side (start 3), term-size cap `s` (start `2 * max(size n1, size n2)`), stop at the first common term. Reverse steps grow terms, so the size cap is what keeps it finite. No ordering is needed because nothing is added to the rule set during the search.

Promotion. Given a path, the halves are `n1 = m` and `m = n2`; also the single reverse steps that the oriented system lacks (these are the non-terminating ones, already known to cycle: `subdist` vs pull-out), which must not be promoted as rules. Candidates enter the existing miner as a new proposer `midpoint` (same applicability prefilter, same scoring by machine proofs removed).

Pros: attacks the stated gap; reuses the rewriter, the miner and the kernel check; the probe is cheap. Cons: branching (about 4 rules x 2 directions x subterms) is large at depth 3 on terms of size 15+; a midpoint may exist only through a detour longer than `d`; the halves may be no more general than the whole (then nothing is gained over the goal proposer); promoting rules from a path risks reintroducing cycles, which the miner's `RULE_BUDGET` guard already contains.

Probe before building (go/no-go). For the 13 unsolved stragglers, run the bidirectional search only and print per straggler: found or not, depth, `m`, and whether either half is smaller than the whole. Go if at least about 5 of 13 have a midpoint at depth <= 3; if none do, the detour needs more than local rewriting and the line stops (option 4). The probe needs the list of the 13, which is not saved; the first step is to have the miner dump uncovered stragglers (`RULEMINER_SHOW`-style) for the deep add3 run.

### 83a. Midpoint probe result

Built the probe (`RULEMINER_MIDPOINT=<depth>`, end of `rule_miner`; `scripts/experiments/mid.sh`, log `logs/mid.out`): for each uncovered straggler, bidirectional search from the two normal forms under the base and chosen rules, one step = any rule in either direction, commutation or association of add/and/or/xor, terms capped at twice the larger side. Run on deep add3 with the `mined` proposer, the §80 settings (51 of 64 covered, 13 uncovered; 6 threads, BelowNormal, machine at ~50% CPU from other sessions, Defender RTP off).

**Result: a midpoint at depth <= 3 per side for 12 of 13** (go threshold was about 5): 3 at depth 1+1, 8 at 2+2, 1 at 2+3; none for `sub(sub(0, x), z) = sub(sub(y, z), add(x, y))` (2726 + 1910 terms seen). In 11 of 12 the midpoint is no larger than the sides (7 nodes against 7 and 7; one 9). So the gap is not a missing larger detour term: the paths are size-neutral reassociations, e.g. `add(sub(shl1 x, z), y) ~ add(sub(x, z), add(x, y))` via `add(add(sub(x, z), x), y)` (reverse `double`, then association), or `sub(add(x, sub(z,-1)), y)` as the shared form of two terms that differ only in where `sub(., -1)` sits. The miner's order check rejects size-neutral rules unless they are permutative (`RULEMINER_PERM=1`), which is the likely reason they were never chosen.

Caveats. (1) Existence of a path says each step is a sound rule instance, not that the halves generalize to useful rules; that is the next test (feed the halves, abstracted by the goal proposer, to the miner as proposer `midpoint` and count coverage). (2) The probe allows commutation/association steps the rewriter normally handles by canonical ordering, so some depth-1 hits may be normal-form differences rather than missing rules; the 2+2 hits are not. (3) One configuration, one family, 13 stragglers.

### 83b. Order-check control and the `midpoint` proposer

Same deep-add3 settings as §80 (64 stragglers, `PERM=1`, `STEPS=40`, 6 threads, BelowNormal, machine ~50% busy from other sessions, RTP off). Scripts `perm2.sh`, `midprop.sh`, `midprop2.sh`; logs `perm2.out`, `midprop_*.out`, `midprop2.out`.

1. **The order check is not the bottleneck.** `RULEMINER_PERM=2` (no order check at all, only the step budget): **50 of 64**, against 51 with `PERM=1`. The §83a guess that the miner rejects size-neutral rules was wrong: `PERM=1` already admits permutative and tie-broken rules. The miner's candidate set is the limit (59 candidates, one per left side).
2. **New proposer `midpoint`** (`RULEMINER_PROPOSER=midpoint`, depth `RULEMINER_MIDPOINT`, default 3): per straggler, `midpoint_search` between the two normal forms, then the two halves `n1 = m`, `m = n2` with the common context removed (`local_diff`), both directions, at most three variables. Coverage, from the bare base rules: **6 of 64** (126 proposed, 64 provable), against `goal` (whole normal forms as rules, §69) 27 of 64 and `mined` 51. As a stand-alone proposer it is clearly worse.
3. **On top of the mined rules** (`RULEMINER_BASE` = the 8 rules `mined` chose; 16 stragglers remain under them, 13 of which the earlier count called uncovered): the midpoint proposer covers **6 of the 16**, with 4 rules, e.g. `add(sub(sub(y, z), z), x) -> sub(add(x, y), add(z, z))` and `sub(sub(x, y), add(x, z)) -> add(sub(0, y), sub(0, z))`. 10 remain, among them `add(add(x, y), sub(z, -1)) = add(add(y, x), sub(z, -1))`: a plain commutation inside a normal form that the rewriter leaves uncanonicalized, which looks like a separate small bug or gap worth a look.

Reading. The midpoint paths exist (§83a) but turning halves into rules mostly yields rules that are too specific or already implied; the useful ones are the four above. The line adds about 6 of the last 16 on top of the miner, and nothing from scratch. Not a replacement for the miner; a possible second stage.

### 83c. The commutation straggler, a second family, and where the proposer line stands

**The commutation straggler is non-confluence, not a canonical-order bug.** `add(add(x, y), sub(z, -1)) = add(add(y, x), sub(z, -1))` has the same normal form on both sides under the built-in rules. Under the 8 mined rules the sides normalize to `add(sub(y, -1), add(x, z))` and `add(sub(z, -1), add(x, y))` (equal as functions). Dropping the first mined rule, the permutative `add(sub(x, y), z) -> add(sub(z, y), x)`, makes them agree again (`normal_forms` debug test, `NF_RULES`). That rule fires on a `show()` comparison of its instance, so which variable ends up inside the `sub` depends on the surrounding operand order, and it does not commute with the built-in `add` ordering. But it is worth keeping: with it, 134 of 150 deep-add3 laws need no machine proof, without it 112 (`rule_set_kernel_check`, same settings). The straggler is therefore a critical pair of that rule with commutation/association; completing it is what the next mined rule would do (it is `add(sub(y, -1), add(x, z)) -> add(sub(z, -1), add(x, y))`, itself permutative). No change made to `rewrite`.

**Second family, `mix3` (first 1500 laws; `mix3mid.sh`, logs `mix3mid_*.out`).** `mined` from the bare base: **152 of 174** stragglers covered (6 threads, `PERM=1`, `STEPS=40`, 8 rounds). Then the `midpoint` proposer on top of the rules `mined` chose: of the 34 stragglers left under those rules, **9 more covered**. So the second stage helps on both families (deep add3: 6 of 16; mix3: 9 of 34), about a quarter to a third of what the miner leaves. Machine ~20% busy at launch, RTP off.

**Where the proposer line stands.** Candidates from outside the miner's own generator: the rule LM covers 8 of 64 (§79-81, a ceiling set by its training distribution); whole normal forms (`goal`) 27 of 64; midpoint halves 6 of 64 alone but a consistent 25-30% of the miner's leftovers on top. The miner (51 of 64, 152 of 174) remains the workhorse. A pipeline `mined` then `midpoint` is the best configuration measured; the remaining leftovers (10 of 16 on deep add3) contain `xor(_, -1)` and `sub(_, -1)` constants and the critical-pair family above.

## 84. The combined rule set, a second round, and the other families

Setup as §83 (6 threads, BelowNormal, `PERM=1`, `STEPS=40`; CPU 20-50% busy from other sessions, RTP off). Scripts `sw3.sh`, `round2.sh`, `round3.sh`, `fam2.sh`; logs `sw3_*.out`, `round2_*.out`, `round3_goal.out`, `fam2_*.out`.

**Combined sets (mined rules, then the midpoint rules chosen on top)**: `scripts/data/add3_mm_rules.txt` (12 rules: the 8 of §83b plus 4 midpoint rules) and `scripts/data/mix3_mm_rules.txt` (7 rules: 4 mined plus 3 midpoint). Kernel check (`rule_set_kernel_check`, width 4): deep add3, 150 laws, **150 checked, 139 with no whole-term machine proof** (mined 8 alone: 134), 0 unproved; mix3, 1500 laws, **1500 checked, 1475 with no machine proof**, 0 unproved. Scaling sweep (20 laws each, kernel-checked): add3 and mix3 proved 20 of 20 at every width n = 4, 8, 16, 32, 64. Build+check seconds for add3: 4.6, 3.1, 6.2, 17.2, 48.8; mix3: 1.1, 1.1, 2.7, 6.1, 20.1. Machine proofs per width: add3 2 (the hand-tuned 25-rule set of §76 had 1), mix3 0. The midpoint rules are sound at every width tested, not only at the width they were mined at.

**Second round on the add3 set** (11 stragglers left under `add3_mm_rules`): `mined` covers 3, `midpoint` 1, `goal` (whole normal forms as rules, the critical pairs) **5**. Diminishing returns: 6 remain, the commutation critical pair of §83c and four with `sub(_, -1)` / `xor(_, -1)`. None of the three proposers proposes the critical-pair rule for it.

**Other families, `mined` then `midpoint` on top** (cmp.sh settings, built-in rules, `subdist` kept):

| Family | stragglers | `mined` covers | left | `midpoint` on top |
|---|---|---|---|---|
| mul | 2 | 2 | 0 | n/a |
| shl | 5 | 0 | 5 | 0 |
| lt | 28 | 11 | 17 | 0 |
| shr | 43 | 4 | 40 | 1 |

The midpoint stage is not general: it gave 6 of 16 (deep add3) and 9 of 34 (mix3), the two add/sub-heavy families, and 0, 0 and 1 on shl, lt and shr, where the stragglers are constant-and-shift laws rather than reassociations. (The `mined` counts here are the rules' own coverage and match the earlier §74 order of magnitude; shr's `mined` count is low, 4 of 43, as before.)

## 85. Selectable rule sets; the commutation straggler is a loop; what lt and shr lack

**Selectable sets (done).** `RULESET=add3_mm|mix3_mm` adds the §84 sets after the built-in rules (`rule_set()`, `include_str!` of `scripts/data/*_mm_rules.txt`; rule name `ruleset`, so `ABLATE=ruleset` removes it). Unset, behaviour is unchanged (all tests pass). Check: `rule_set_kernel_check` with `RULESET=add3_mm` and an empty rule file gives the same 150 checked / 139 machine-free as the file route. New test `promoted_rule_sets_are_proved`: every rule of both sets is true at widths 1-4 and proved and kernel-checked at width 4. The sets were mined without `ABLATE=subdist`; they are not meant to be combined with the hand-tuned `add3_final`/`mix3_final` sets of §76.

**The commutation straggler is not a missing critical-pair rule; it is a rewriting loop.** Adding either orientation of the candidate rule `add(sub(y, -1), add(x, z)) -> add(sub(z, -1), add(x, y))` to the 12-rule set changes nothing (`normal_forms`, same DIFF). `NF_TRACE` on one side shows a cycle: the permutative `add(sub(x, y), z) -> add(sub(z, y), x)` and `sub(add(x, y), z) -> add(sub(x, z), y)` keep re-firing on the same few terms until `RULE_BUDGET` runs out (the budget is 200 here, 40 in mining), and the "normal form" is wherever the budget stopped. The permutative rule's guard compares `show()` of the whole instance, which is a termination order for that rule alone but not together with a rule that regroups the term. So a critical-pair proposer would not help, and I did not write one. The kernel proofs stay sound (a step is only taken when proved); the cost is that a mined permutative rule can make the normal form depend on the budget, and with it which laws count as stragglers. Options if it matters: (a) detect a repeated term along a rewrite chain and stop there (still not unique); (b) forbid permutative rules in sets used with `sub(add(..), ..)` pulls; (c) a termination order that includes the regrouping rules. Not done.

**What lt and shr lack** (the leftovers in `logs/fam2_lt_mined.out`, `fam2_shr_mined.out`):
- **shr, 39 left: 22 are `0 = shr1(t, 0)` with `t` a closed term equal to 1** (`sub(0, -1)`, `sub(-1, add(-1, -1))`, `sub(add(0, 0), -1)` ...), plus shr1 laws of the form `shr1(x, 0) = shr1(xor(x, sub(0, -1)), 0)`. The rewriter has constants `0` and `-1` only, no constant folding and no `1`, so these cannot normalize. A `One` term (or evaluating closed terms at the width) would remove the 22; the rest (17) are laws whose two arguments differ only in the lowest bit, which `shr1` discards: `shr1(add(x, x), 0) = shr1(sub(add(x, x), -1), 0)`. They need a rule family "`shr1(t)` ignores bit 0" (e.g. `shr1(add(x, x)) = shr1(sub(add(x, x), -1))`), which the abstraction-based miner cannot reach.
- **lt, 17 left of 28**: comparisons such as `lt(add(x, y), x) = lt(xor(y, -1), xor(0, x))` (overflow of `x + y`) and `lt(x, add(x, x))`. Their sides are inequalities decided by the carry out, not by rewriting with equalities between terms; this is the carry-chain reasoning the machine proofs do. Expect those to stay machine proofs unless an `lt`-specific lemma set (overflow tests) is added by hand.

Hence the leftovers per family have different causes: add3/mix3, a loop from permutative rules; shr, missing constant folding and bit-0 insensitivity; lt, carry-out comparisons.

## 86. Loop guard in the miner, and constant folding

**`RULEMINER_NOLOOP=1`.** `rule_step` counts, per term, how often it fires (`RULE_SEEN`, only while the miner scores a candidate set); a candidate set under which some law exhausts the step budget with a term rewritten 3 or more times is rejected as cyclic (exhaustion alone is not enough: long legitimate derivations also hit the budget at `STEPS=40`). Deep add3, `mined`, the §80 settings (`noloop.sh`, `logs/noloop.out`): **43 of 64** stragglers covered against 51 without the guard, with 8 rules (`add(sub(x, y), z) -> add(sub(z, y), x)` still first). The commutation straggler of §83c is gone from the uncovered list. So the loops bought 8 of the 51; those 8 laws were still proved and kernel-checked, but through budget-dependent normal forms. A choice, not a bug: guard on for sets that must have unique normal forms, off for maximum coverage.

**Constant folding (`fold_rule`, `ABLATE=fold`).** A closed term (no variables, no `shr1`, not `lt`) equal at widths 1-6 to `0`, `-1` or `1` (written `sub(0, -1)`; adding a `One` constructor would touch the ~68 `Ones` sites, the per-position provers and the machines) is a rule `t -> constant`, proved by `prove_rule` like any rule. Effect on straggler counts under the built-in rules (cmp.sh settings): **shr 43 -> 24**, lt 28, mul 2, shl 5 unchanged. Scaling sweep, 40 laws per family, n = 4, 8, 16, 32, kernel-checked: all proved (shr, mul, lt, shl), machine proofs per width now shr 0 (was 1), shl 0 (was 1), lt 1 (was 3 at 4-64 in §82), mul 0. Test `closed_terms_fold_to_constants`.

**Why not all 22 of the closed-term shr stragglers.** Terms containing `shr1` are excluded because `prove_rule` cannot prove laws over `shr1` (it is not a machine; the root shift laws are proved by the per-position prover instead), so `shr1(sub(0, -1)) = 0` itself is still not rule-provable; the fold only reduces the argument. Of the 43, 19 are now closed; 24 remain.

Also unchanged: the bit-0-insensitivity family and lt's carry-out laws of §85.

## 87. shr rules, loop-free pipelines, and a tie-break order for permutative rules

Same machine conditions as §83-86 (6 threads, BelowNormal, `PERM=1`, `STEPS=40`). Scripts `shrmine.sh`, `shrgoal.sh`, `pipe.sh`; logs `shrmine.out`, `shrgoal.out`, `pipe_*.out`, `swnl_*.out`.

**shr rules are now provable (`prove_rule`, root `shr1`).** §86 left the closed shr stragglers; a probe showed laws like `0 = shr1(sub(0, -1))` are already closed machine-free by `shr_mask_eq`, so the real gap was that the miner could not state a rule with a `shr1` root (`prove_rule` handles only machines). `prove_rule` now proves laws with a `shr1` root on both sides (or `0` on one side) through `rewrite_law` itself, with the rule being proved hidden from `rule_step` (`PROVING`), so it cannot appear in its own proof. Effect, shr family (900 laws), stragglers: 43 (§82) -> 24 (fold, §86) -> `mined` covers 8, leaving 17 -> `goal` on top covers 6, leaving 11. First rule chosen: `shr1(sub(0, -1), 0) -> 0`. Remaining 11 are the bit-0-insensitivity laws with arithmetic arguments (`shr1(add(sub(x, -1), y)) = shr1(add(sub(y, -1), x))`, the `xor(xor(x, y), -1)` regroupings).

**Loop-free pipeline (`RULEMINER_NOLOOP=1`, fold on): `mined`, then `midpoint`, then `goal`, each on top of the last** (`scripts/data/add3_nl_rules.txt`, 15 rules; `mix3_nl_rules.txt`, 10 rules; selectable as `RULESET=add3_nl|mix3_nl`):

| Stage (stragglers under the previous stages' rules, covered by the stage) | deep add3 | mix3 |
|---|---|---|
| `mined` | 64, covers 43 | 174, covers 122 |
| `midpoint` on top | 24, covers 8 | 177, covers 12 |
| `goal` on top | 16, covers 11 | 165, covers 102 |
| left after all three | 5 | 63 |

(The straggler count at a stage can exceed the previous stage's remainder: "covered" means fewer machine proofs than at the stage's own base, so a partly fixed law still counts. Details in `logs/pipe_*.out`.) Kernel check (width 4): add3 **150 checked, 133 machine-free**, mix3 **1500 checked, 1437 machine-free**, 0 unproved; the looping sets of §84 had 139 and 1475, so the loop guard costs 6 and 38 laws. Scaling sweep of the `nl` sets, 20 laws, n = 4..64: all proved and kernel-checked; add3 build+check 7.0, 5.9, 10.9, 34.3, 83.8 s with 2 machine proofs per width; mix3 1.6, 1.4, 3.1, 7.7, 32.0 s with 0.

**A tie-break order for permutative rules (`PERM_ORDER=tie`).** The `show()`-only guard is not a simplification order (`show(add(x, y)) < show(x)`), which is why mined permutative rules loop with regrouping rules. With `PERM_ORDER=tie` the instance must go down in `tie_greater` (the order that already orients the non-permutative tie rules), and only if that does not separate the two terms does `show()` decide. Result on the add3 sets: the commutation law normalizes to the same form on both sides under `add3_mm` (it did not before), but `add3_mm` machine-free laws drop from 139 to 124: the coverage the loops bought is budget luck, as in §86. The loop-free `add3_nl` set is unaffected (133 either way). Not proved terminating; it is a guard that removed this loop, nothing more. Default stays `show()`.

Reading. With the loop guard or the tie order, the loops' extra coverage disappears and the sets lose 6 (add3) to 38 (mix3) machine-free laws of 150 / 1500; in exchange normal forms are the same on both sides of the commutation law and no budget accident decides proofs. Which to prefer depends on whether unique normal forms matter (e.g. for a rewriter used as a decision procedure) or only proof coverage.

## 88. A built-in rule for shifted nots, and a prover branch for shifted bitwise terms

The 11 shr leftovers of §87 were two different things. Seven are arithmetic laws equal modulo bit 0 (`shr1(add(x,x))` against `shr1(add(x, sub(x,-1)))`, the commutation-style laws); they are *proved*, by a whole-term machine, and only a rule could take the machine out, which the miners did not find. The other four involve a bitwise not: `notsub` rewrites `xor(x,-1)` to `sub(-1,x)` bottom-up, which blocks `shrdistxor` above it, so `shr1(sub(-1, xor(x,y)))` and `xor(shr1 y, xor(shr1 -1, shr1 x))` never met, and `prove_eq` had no way to close even the xor-of-shifts pair once they did.

Two additions, both checked by the kernel:

- **`shrnot`** (built-in, `shr1(sub(-1,x)) -> xor(shr1(x), shr1(-1))`). Its proof (`shr_not_law`) goes through the middle term `shr1(xor(x,-1))`: the rewriter proves it equal to the left side with `notsub` on and to the right side with `notsub` off (neither using `shrnot`, via `PROVING`), and the two compose.
- **`prove_eq` branch for add-free terms with shifts**: when both sides are add-free, contain a shift, and agree exhaustively at widths 1..=5 (k <= 3), close by `bitwise_law_k` (`pos_law`). Before, only aligned bitwise terms (`abstract_atoms`) reached the bitwise prover.

Test `shrnot_rule_is_provable_and_closes_the_shr_not_laws` (n = 4, 8, kernel-checked, no machine proof). Result on the §87 shr run (`shrnot.sh`, `logs/shrnot_mined.out`, same settings, 6 threads): built-in stragglers 24 -> **20**; `mined` still covers 8, leaving **12** (was 16). The 12 are the arithmetic laws above, still machine proofs. Counts only; no timings.

Reading. The bitwise-not part of the shr gap is closed by one rule plus one prover branch. What remains is the same confluence problem as the commutation straggler (§83c, §85): equal arithmetic terms with different normal forms, here under a shift that discards bit 0. A bit-0 lemma does not help, since the machine proof of `A & M = B & M` is the arithmetic law itself.

**Other families (check, 2026-10-04, `s88fam.sh`, `logs/s88fam.out`).** `mined` on mul, shl, lt and deep add3 after section 88: stragglers/covered 2/2, 5/0, 28/11, 64/51, identical to §84 and §80. Load: CPU 63% from another session, RTP off, BelowNormal, 6 threads; counts only.

## 89. A path order for weight-tied rules (`PERM_ORDER=lpo`): sound, but it costs coverage

Probe of §85 option (c). `lpo_greater` is a lexicographic path order with a total precedence (leaves below operators, operators by `head_prec` then index); test `lpo_is_a_strict_total_order_closed_under_contexts` checks it is irreflexive, total and context-closed on all terms of up to 4 nodes over two variables. With `PERM_ORDER=lpo`, `rule_step` applies a rule that ties in the weight order (permutative or tie-broken) only when its instance goes down in this order; unlike the `show()` guard it is closed under contexts, so a permutative rule can no longer be undone by a regrouping rule in a larger term. Default and `tie` unchanged. Script `lpo.sh`, log `logs/lpo.out`; CPU about 54% from other sessions, RTP off, 6 threads, BelowNormal, counts only.

| Order | `add3_mm` machine-free of 150 | `add3_nl` machine-free of 150 | `mined` on deep add3, covered of 64 |
|---|---|---|---|
| `show()` (default) | 139 | 133 | 51 |
| `tie` (§87) | 124 | 133 | 41 |
| `lpo` | 99 | 106 | 28 |

(The fixed sets were mined under the default order and not re-mined for `tie` or `lpo`.) The `lpo` run chose 8 rules, none of the middle-pair rules of the default run; the uncovered list now contains plain reassociations such as `add(sub(x, z), y) = sub(add(x, y), xor(z, 0))`. **Reading:** a principled reduction order removes the budget-luck coverage of §86-87 and then some, because an instance-wise path order orients rules in directions the machine-proved laws did not need, and the miner's candidate filter (`rule_order_or_tie`) still proposes rules for the old orientation. Not worth adopting as the default; it shows the unique-normal-form price is large (43 to 28 here against 43 with the loop guard). Not measured: whether re-orienting the miner's candidates under `lpo` recovers coverage, or whether the commutation law normalizes to one form under `lpo`.

### 89a. Re-mining under `lpo`, and the commutation law

`rule_order_or_tie` now admits both directions of any weight-tied rule under `PERM_ORDER=lpo` (the instance check in `rule_step` orients them). Script `lpo2.sh`, log `logs/lpo2.out`, same machine conditions as §89, counts only. Deep add3, `mined`:

| Order | Covered of 64 | Machine-free of 150 under its own mined set | Commutation law of §83c |
|---|---|---|---|
| default | 51 | 134 | DIFF (`add(sub(y,-1), add(x,z))` against `add(sub(z,-1), add(x,y))`) |
| `lpo` | 28 | 114 | SAME |

The `lpo` run chose exactly the same 8 rules as before the filter change, so the coverage loss is not an orientation mismatch in the miner's filter: the candidate generator (equal pairs of the pool, at most two variables per candidate) simply has no candidate for the reassociations the default order closes through loops. Under `lpo` the commutation straggler normalizes to one form, so the order does what it should; the price is 23 covered laws of 51. The remaining gap sits in the generator, not the order.

### 89b. The pipeline under `lpo`

Deep add3, `mined` then `midpoint` then `goal`, each on the previous rules, `PERM_ORDER=lpo`, no loop guard (`lpo3.sh`, `logs/lpo3.out`, rules in `logs/lpo3_rules.txt`; §89 machine conditions, counts only). Stage by stage (stragglers under the earlier stages' rules, covered by the stage): `mined` 64, covers 28; `midpoint` 36, covers 5; `goal` 36, covers 16. 19 rules; kernel check under `lpo`: **150 checked, 125 machine-free**, 0 unproved. For comparison: the loop-free default pipeline (§87, 15 rules) 133, the looping `add3_mm` 139. Against `mined` alone under `lpo` (114 machine-free, �89a) the two later stages add 11, and `goal` does most of it, as in �84. `lpo` ends 8 laws behind the loop-free default pipeline and 14 behind the looping set, in exchange for a provably context-closed termination order. Uniqueness of the normal forms was checked only on the commutation law (§89a), not across all laws.

### 89c. Confluence across the law set, and mix3 under `lpo`

`rule_set_kernel_check` now also prints `NFSAME`: how many of its laws have equal normal forms on both sides (`lpo4.sh`, `logs/lpo4.out`, mix3 rules in `logs/lpo4_mix3_rules.txt`; machine conditions as §89, counts only). Machine-free proofs / laws with equal normal forms:

| Set (order) | add3, 150 laws | mix3, 1500 laws |
|---|---|---|
| built-ins only (default and `lpo`) | 86 / 86 | |
| looping `_mm` set (default) | 139 / 141 | 1475 / 1478 |
| loop-free `_nl` set (default) | 133 / 137 | 1437 / 1437 |
| `lpo` pipeline (`lpo`) | 125 / 125 | 1407 / 1407 |

mix3 under `lpo`: `mined` 174 stragglers, 156 covered; `midpoint` 72 left, 0 covered; `goal` 66 of 72 covered; 10 rules, 1407 machine-free, 93 laws still on whole-term machines (the default loop-free set: 63).

Reading. (1) Under `lpo` equal normal forms and machine-free proofs coincide exactly, as they should when the normal form is unique and a proof needs nothing else. (2) The default sets reach equal normal forms on *at least as many* laws as the `lpo` sets (141 and 137 on add3, 1478 and 1437 on mix3 against 125 and 1407), so on this law set the default order is no less confluent than `lpo`; the guarantee `lpo` gives is for all terms, which this metric does not test. (3) The cost of `lpo` on mix3 is 30 laws against the loop-free set and 68 against the looping one, so the 8-law gap on add3 does not shrink at 10 times the laws. (4) On mix3 `midpoint` adds nothing under `lpo`; the whole gain after `mined` is `goal`.

## 90. Hand-written bit-0 rules for shr: one law each, the add3 set does more

Scripts `shrset.sh`, `shrbit0.sh`, `shrbit0b.sh` (logs `logs/shrset.out`, `shrbit0.out`, `shrbit0b.out`); same machine conditions as §89, counts only. The 12 shr leftovers of §88 are, in fact, mostly *arithmetic* confluence failures inside `shr1` (`shr1(add(sub(x,-1), y))` against `shr1(add(sub(y,-1), x))` are equal as plain sums) and only some are bit-0 laws (`shr1(x) = shr1(xor(x, 1))`, `0 = shr1(and(x, 1))`, `shr1(add(x,x)) = shr1(add(x,x)+1)`).

- **The add3 rule sets already take most of them.** Stragglers of the shr family under `RULESET`: built-ins 20, `add3_mm` 10, `add3_nl` 11, `mix3_mm` 13, `mix3_nl` 15. Kernel check of all 900 shr laws: machine-free 880 built-ins only, 890 with `add3_mm` (NFSAME 827 and 837).
- **Eight hand-written bit-0 rules** (`scripts/data/shr_bit0_candidates.txt`, fed through the `file` proposer) are all provable, but only one passes the miner's applicability prefilter (a left side must match a subterm of a straggler's *normalized* terms; the others do not, because the arguments are rewritten first): `shr1(sub(x, xor(x,-1)), 0) -> shr1(add(x,x), 0)`, +1 law. Kernel check with all eight added: 881 machine-free (built-ins) and 891 (`add3_mm`), NFSAME 829 and 839, against 880/890 and 827/837 without.

Reading. Hand rules at the surface form of the leftovers do not reach them, because by the time `shr1` sees its argument, the argument is already in the normal form the other rules chose, and the bit-0 law has to be stated over *that* form. A rule would have to be stated over normal forms (or the shr bit-0 reasoning built into the rewriter, e.g. normalizing the argument of `shr1` modulo bit 0), so the line looked like a prover feature; §90a corrects this. The cheap gain is available already: use `add3_mm` for shr (880 to 890 machine-free).

### 90a. Rules stated over the normal forms do work

`normal_forms` on the 10 `add3_mm` shr leftovers shows what `shr1` sees: `shr1(sub(shl1(x,0), -1), 0)` against `shr1(shl1(x,0), 0)` (even plus one), `shr1(sub(x, xor(x,-1)), 0)` (that is `2x+1`), `xor(shr1(sub(0,-1),0), shr1(x,0))`, and `shr1(sub(x, xor(y,-1)), 0)` against `shr1(add(sub(x,-1), y), 0)`. Four rules over these forms (`scripts/data/shr_bit0_nf.txt`, `file` proposer, `shrbit0nf.sh`, log `logs/shrbit0nf.out`): three are provable and chosen, `shr1(sub(0,-1),0) -> 0`, `shr1(sub(x, xor(x,-1)),0) -> shr1(shl1(x,0),0)`, `shr1(sub(shl1(x,0),-1),0) -> shr1(shl1(x,0),0)`, covering **6 of the 10** stragglers; the fourth (`shr1(sub(x, xor(y,-1)),0) -> shr1(add(sub(x,-1),y),0)`) is not provable by `prove_rule` as a rule. Kernel check of all 900 shr laws under `add3_mm` plus the three rules: **896 machine-free** (890 without), NFSAME 864 (837). The 4 left are plain sums, `x+y+1` and `x+x` written through `sub`/`xor(_, -1)`: `shr1(add(sub(x,-1),y)) = shr1(sub(x, xor(-1,y)))` and its mirror, `shr1(add(x,x)) = shr1(add(x,sub(x,-1)))`, `shr1(add(x,x)) = shr1(sub(x, sub(-1,x)))`. So §90's reading needs a correction: the bit-0 laws *are* reachable by rules, but only stated over the normal forms the rewriter produces (a human, or a proposer fed the `normal_forms` output, can write them; the miner's own candidate generator did not). `miner_summary.sh` now defaults the shr family to `RULESET=add3_mm` (its `mined` stage covers 4 of the 10 on top; 29 s, CPU 71% from other sessions, RTP off).
