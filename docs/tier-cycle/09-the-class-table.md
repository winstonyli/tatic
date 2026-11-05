## The class table

### Canonical forms: from the survey to the table's phase 1 (2026-10-22/23)

*Canonical forms: hand-coded or learned (survey, 2026-10-22; literature in `RELATED_WORK.md` §81).* The laws the join
cannot reach at any budget ("What the join can't reach") need pure-bitwise identities and bitwise-arithmetic bridges.
The miner cannot propose the first kind: its candidates come from subterms that use add or sub
(`miner.rs`, `candidates`), and the bitwise collapse (`rewrite.rs`, `abstract_atoms` and the `LawKind::Bitwise` step)
maps a bitwise node only to 0, -1 or one of its atoms. One normal form for a whole region of add, sub, shl1 and bitwise
operators over atoms (subterms rooted at `lt` or `shr1`) would replace the collapse, `notsub`, the root-only operand order
and the hand rules, each rewrite one law the kernel proves (`bitwise_law_k`, or `add_tree_law` within `CARRY_CAP`).
Options, by end state:

| option | covers | learned or fixed | limit |
|---|---|---|---|
| a. linear-MBA form: coefficients over conjunctions of atoms (SiMBA) | pure-bitwise laws, bridges, `notsub`, operand order | fixed theory | 2^k in atoms; laws across carry-sensitive atoms |
| b. smallest term per truth table | pure-bitwise laws only | fixed | no bridges; a subset of c's table |
| c. learned table: enumerate terms over k ≤ 3 atoms, group by values at several widths (`pool_conjectures`), the smallest member of each class is its representative, rewrite each node bottom-up to it | what a and b cover, within the enumerated sizes, and every mined rule inside that range | classes and representatives learned; evaluation and the order fixed | classes past the enumeration, unless children reduce into range; small-width collisions fail their proofs and are dropped |
| d. learned structure on c: integer relations among the class values mod 2^n, a basis of smallest terms as coordinates | a without coding it, past c's sizes | learned | speculative; needs a solver mod 2^n; carry cap |
| e. complete the mined rules (critical pairs, `rewrite::critical_pairs`) | what the rules' overlaps imply | learned | in-sample: cmp3d's floor 72 to 30, add3's and sbo3's unmoved ("Completion on the floor"); blind where the miner is |
| f. the GPU model as a learned signature or proposer | proposals only | learned | not canonical alone; a later layer on c |

Not decided; leaning c, with d as its additive extension, for the goal of a kernel that improves itself; a stays the fallback if
c's range is too small. ANF (bitwise only, `or` grows to three monomials) is out: a covers it and more.
Polynomials mod 2^n and the nonlinear MBA tools are out: no bitwise operators, or no canonical form and no proofs. The
cheapest test of c is in the next paragraph.

*A learned table of representatives: the probe (2026-10-22; runs `2026-10-22-class-table`, 6 s, CPU 32% at launch, and
`-class-table-400k`, 22 s; exe dabc018 plus `docs/runs/2026-10-22/patches/class_table.patch`, test
`rewrite::class_table_probe`, reverted; script `docs/runs/2026-10-22/scripts/class_table.sh`).* Terms over x, y, z, 0,
-1 and add, and, or, xor, sub are enumerated by size from representatives only. Each is keyed by its exhaustive values at
widths 3 and 4, hashed to 128 bits, and the first (smallest) of a class is its representative. Each law's two sides are
normalised bottom-up, each node to its class's representative, with no rules, no join and no proofs, and the laws whose
sides meet are counted. Against the ref library at `JOIN_VISIT` 1000 (free laws, kernel-checked, join included; run
`2026-10-22-join-budget`):

| held-out set | ref library | table ≤ 7 (7547 classes) | table ≤ 9 (140596 classes, 7.7 s) | ≤ 11, capped at 400000 classes |
|---|---|---|---|---|
| add3's 15 left at 20000 ("What the join can't reach") | 0 | 13 | 15 | 15 |
| add3 size 9 / 11 | 191 / 169 | 165 / 150 | 200 / 186 | 200 / 191 |
| sbo3 size 9 / 11 | 174 / 164 | 189 / 151 | 200 / 195 | 200 / 199 |
| mix3 size 9 / 11 | 169 / 153 | 187 / 154 | 200 / 194 | 200 / 196 |
| cmp3d size 9 / 11 / 13 | 198 / 198 / 190 | 143 / 131 / 118 | 143 / 133 / 122 | 143 / 133 / 122 |

- **Within its operators, the table alone beats the mined rules and the join.** At ≤ 9 every size-9 law of add3, sbo3
  and mix3 meets. At size 11 the table meets 186-195 laws per family, against the library's 153-169.
- **cmp3d stays where the table can't reach.** `lt` is not among the table's operators. Its one-bit result is a second
  sort and would get its own classes (the signature already tells the sorts apart in `pool_conjectures`).
- **No merge was wrong where checked.** All 3967 replacements at ≤ 9 agree at width 8 on the screen's 204 inputs. So
  normalising keeps each side's value there, and unequal sides could not meet. Equal values at widths 3 and 4 are still
  only a conjecture: each replacement needs its kernel proof, whose cost and carry cap are not measured.
- **Cost.** ≤ 9 is 140596 classes, 7.7 s and about 650 MB of value vectors (4.6 KB each). Size 11 adds over 259404
  classes before the cap, so a full ≤ 11 would take several GB. The table depends only on the operators, not on a
  family's laws. It is over three variables. Terms with more, or with non-table operators below a node, would need
  `abstract_atoms`' abstraction first.

*The table with `lt` as a second sort, its proofs, and smaller keys (2026-10-22; run `2026-10-22-class-table2`, 87 s,
CPU 36% at launch; exe dabc018 plus `docs/runs/2026-10-22/patches/class_table2.patch`, reverted; script
`docs/runs/2026-10-22/scripts/class_table2.sh`).* The table now also has `shl1`, and `lt` of two representatives as a
one-bit sort that no operator consumes (its key carries the sort). Each distinct replacement is checked against every
width-4 input and the screen's width-8 inputs; one failing either is a suspect. The others are proved at width 4
(`prove_checked`, then `bitwise_law_k` for carry-free ones) and kernel-checked.

| held-out set | ref library, `JOIN_VISIT` 1000 | ≤ 9, exhaustive key | ≤ 9, 64-input key | ≤ 11, 64-input key, capped at 4M classes |
|---|---|---|---|---|
| add3's 15 left at 20000 | 0 | 15 | 15 | 15 |
| add3 size 9 / 11 | 191 / 169 | 200 / 189 | 200 / 189 | 200 / 200 |
| sbo3 size 9 / 11 | 174 / 164 | 200 / 198 | 200 / 198 | 200 / 200 |
| mix3 size 9 / 11 | 169 / 153 | 200 / 195 | 200 / 195 | 200 / 200 |
| cmp3d size 9 / 11 / 13 | 198 / 198 / 190 | 200 / 197 / 191 | 200 / 198 / 192 | 200 / 200 / 199 |
| classes (of them `lt`) | | 235899 (69955) | 222747 (56544) | 4000000 (879633) |
| enumeration | | 10.8 s, 4608 B per class | 0.45 s, 72 B per class | 8.6 s |
| distinct replacements, suspect | | 3203, 0 | 3240, 68 | 3298, 70 |

- **One mechanism covers both sorts.** With `lt` as a second sort, cmp3d goes from 143 / 133 / 122 to 200 / 197 / 191,
  and `lt` needs no code of its own beyond its sort.
- **Every replacement has a proof.** All 3203 of the exhaustive key's replacements are proved and kernel-checked at
  width 4: 2820 by `add_tree_law` (carry encodings), 383 by `bitwise_law_k`. None is over `CARRY_CAP` or without a
  proof. Proving took 52 s and checking 12 s, about 20 ms each; the slowest took 1.1 s
  (`add(y, add(x, add(z, and(x, y)))) = add(x, add(y, add(z, and(x, y))))`, a permutation).
- **A smaller key is about 64 times smaller and 24 times faster, but merges wrongly.** On 64 pseudo-random width-8 tuples
  plus the 8 tuples of 0s and 1s, 68 of 3240 replacements are suspect (103 with 16 tuples); which functions collide is
  not looked at. That key has 13411 fewer `lt` classes but 259 more bit-vector classes at size 9: the exhaustive key's
  widths 3 and 4 also merge some terms that differ at width 8. None of those merges was used here (0 suspects), but
  neither key is sound alone. The meets in the random-key columns include laws normalised through a suspect
  replacement, so they are an upper bound. Every replacement needs a proof anyway, so a wrong merge would cost a failed
  proof and that class's coverage, not soundness.
- **At ≤ 11 the table meets 2203 of the 2204 laws**, an upper bound as above. Its 4M classes (capped partway through size
  11) took 8.6 s.

*How much random testing is worth (2026-10-22; run `2026-10-22-claim-calibration`, 38 min, CPU 49% at launch from
other sessions; exe 1962b46 plus `docs/runs/2026-10-22/patches/claim_calibration.patch`, reverted; script
`docs/runs/2026-10-22/scripts/claim_calibration.sh`).* A first calibration point for a probabilistic layer between the
kernel and a proposer: how likely a claimed equality is to be proved, given the random tests it passed. The claims are
the merges a key proposes while the table above is enumerated to size 9: 20000 sampled uniformly per key. Each is
refuted by a difference on 4096 fresh random width-8 inputs, on every width-4 input or on the screen, or else proved as
above. For a refuted claim, the share d of the 4096 inputs it differs on gives its chance of passing n more random tests,
(1 − d)^n. That gives P(proved | passed n more) for each kind of claim. Proving stopped at 10 minutes per key, so 40-53% of
the last three keys' unrefuted claims were not tried. They are counted as proved: of the 39664 unrefuted claims that
were tried, 39645 were proved and 19 (all `lt`) found no proof.

| key (merges proposed) | kind | claims | refuted (differ on ≤ 1% / ≤ 10% / more) | P(proved), n = 0 / 8 / 64 / 256 more tests |
|---|---|---|---|---|
| 8 Boolean tuples (370270) | bitwise | 309 | 0 | 1 |
| | add/sub | 10149 | 4972 (0 / 5 / 4967) | 0.510 / 0.997 / 1.000 / 1.000 |
| | shl1 | 6389 | 2098 (0 / 0 / 2098) | 0.672 / 1.000 / 1.000 / 1.000 |
| | `lt` | 3153 | 2697 (234 / 61 / 2402) | 0.145 / 0.569 / 0.727 / 0.878 |
| | all | 20000 | 9767 | 0.512 / 0.966 / 0.984 / 0.994 |
| plus 4 random (652823) | all | 20000 | 3585 (358 / 192 / 3035), 2671 of them `lt` | 0.821 / 0.961 / 0.983 / 0.993 |
| plus 64 random (598918) | add/sub | 10510 | 1 (0 / 1 / 0) | 1.000 |
| | `lt` | 2055 | 836 (601 / 233 / 2) | 0.592 / 0.610 / 0.704 / 0.855 |
| | all | 20000 | 837 | 0.958 / 0.961 / 0.974 / 0.989 |
| exhaustive widths 3 and 4 (585766) | shl1 | 7293 | 36 (0 / 0 / 36) | 0.995 / 1.000 / 1.000 / 1.000 |
| | `lt` | 1610 | 0 | 0.994 (10 without a proof) |
| | all | 20000 | 36 | 0.998 / 0.9995 / 0.9995 / 0.9995 |

("≤ 1%" counts claims that differ on 0-40 of the 4096 inputs; the 5, 10 and 21 that differ on none of them were caught at
width 4 or on the screen.)

- **What a test is worth depends on the kind of claim.** A wrong arithmetic merge (add/sub or shl1) differs on most
  inputs, so 8 random tests take P from 0.51-0.67 to 0.997-1.000. A wrong `lt` merge differs on few inputs, its result
  being one bit: 256 more tests take it only to 0.85-0.88. A 64-input key has already removed every `lt` merge that
  testing catches easily, so for its `lt` claims further testing is worth almost nothing (0.59 to 0.61 after 8).
- **Bitwise merges were never wrong, under any key.** On the 8 tuples of 0s and 1s a pure bitwise term's values are its
  truth table, which decides it at every width. That is a decision, not a probability.
- **The exhaustive small widths are the right evidence for `lt`, and random width-8 tests for what they miss.** The
  exhaustive key refutes no `lt` claim, and its only wrong merges are 36 shl1 claims (presumably shifts that lose bits at widths 3 and
  4), each differing on at least 10% of width-8 inputs, so 8 random tests leave P at 1.000.
- **So one calibrated layer, with the claim's shape as a feature and proof outcomes as labels, would learn these
  differences**, rather than hand-set test counts per kind. The labels cost little: 39645 claims were proved, and the 19
  without a proof are all `lt`.
- **Limits.** The claims are enumeration merges over three variables up to size 9, not laws from a stream, so the
  numbers hold for that distribution only. Differences were measured at width 8; the proofs are generic.

*The belief layer's calibration milestone stops at its first gate (2026-11-01; runs `2026-11-01-belief-dump-all-2`, 5 min,
at commit 72c992d (clean tree), and its pilot `2026-11-01-belief-pilot-plus64-b`; code `crates/church-bv/src/belief.rs`, no patch;
report text in the dump run's `report.log`; a first dump, `2026-11-01-belief-dump-all`, gave the same totals and gate
result before a review moved `shr1` claims out of the bitwise kind; spec `docs/superpowers/specs/2026-10-31-belief-layer-design.md`).* The dump re-draws
the claims with `Classes::build` (20000 merges per key, the four keys of 2026-10-22; its enumerator differs, so the mix
is new) and labels each claim with evidence kept apart from the label: refuted if it differs on 4096 fresh random
width-8 inputs (S2), on 256 more (S1, disjoint from S2), on a width-4 input or on the screen; proved if the class
table's prover finds a proof; else unproved. The pilot ran 1000 claims in 3.5 s, so every sampled claim is tried (cap
20000) and the untried bias of 2026-10-22 is gone. Of the 80000 claims, 60691 are proved, 2693 unproved and 16616
refuted; the kernel-path check (a full proof of each proved claim whose sample index is a multiple of 20) agreed on 3058 of 3058.

- **No claim that passes the screen is refuted.** 63384 claims pass every width-4 input and the screen; none differs on
  any of the 4352 further random inputs. All 16616 refuted claims fail width 4 (370 only there), the screen (27 only
  there) or both (16219). The stage-1 gate needs 100 such hard negatives in all and 10 per fold; it found 0, so
  stage 2 (the smoothed-count and logistic arms, the paired bootstrap against the screen) did not start, as the spec
  prescribes. The finding is "too few hard negatives to compare": on this claim distribution the screen plus the exhaustive
  width-4 check leave nothing for a belief about refutation to rank. With 0 of 63384 claims falsified, the one-sided 95%
  bound on the share of screen-pass claims that a further 4352 random inputs falsify is about 4.7e-5 (3/63384). Why none:
  1434 refuted claims differ on 1-40 of the 4096 inputs, and all but one of them already fail the exhaustive width-4 check
  (370 claims fail only that check), so the width-4 check removes what random tests find hardest; the 27 that pass it and
  fail the screen predict about 0.5 slipping past the screen's 202 random inputs.
- **What is left to predict is unprovability.** 2693 screen-pass claims (4.2%) have no proof: 2293 shift claims (`shl1` or `shr1`), 400 `lt`, no
  add/sub, spread over the keys (bool8 315, plus4 590, plus64 807, exhaustive 981). 2652 of the 2693 contain `shr1`, which
  `verdict` turns into a fresh variable (an inference: that makes a proof unavailable when the shift's value matters). None is refuted by the further inputs, so
  they look true but out of the prover's reach (an inference; a proof or counterexample at another width would confirm
  it). The spec scored this as A_unp, descriptive only, so the milestone's headline score is empty and the live one is
  the secondary. The 2026-10-22 run found 19 such claims (all `lt`); the new enumerator proposes `shr1` claims the old one
  did not, and nearly all the new unproved ones contain `shr1`.
- **Not done.** The estimators and their comparison (counts, logistic, bootstrap) were not run. What is kept:
  `belief_counts`, `cells_at`, the grouped folds, `logistic_fit`, AUC and the paired bootstrap, each with a unit test.
  Under the new enumerator some bool8 and plus4 merges that contain `shr1` are wrong, so the 2026-10-22 line "bitwise
  merges were never wrong, under any key" holds only for claims without `shr1` (kind "bitwise" now excludes `shr1`). A
  rerun on a different label (unprovable as the negative class) is parked in `PARKED.md`, "Belief layer stage 2".
- **The unproved ones are provable (spike, 2026-11-01).** All 2693 unproved screen-pass claims (2652 with `shr1`, 41 `lt`
  without) hold on every width-6 input (3 variables, 262144 inputs), and `prove_rule` (the every-input route, kernel
  checked at width 4) proves all 2693, about 0.3 s each (runs `2026-11-01-belief-shr1-spike-3` for claims 1-1350 and
  `-spike-4` for 1351-2693; the first two runs died of memory, since the spike's width-6 memo and job grew with every
  claim, so it now renews both every 50 claims). So "unproved" labels the table's `verdict` path (a carry encoding with
  each `shr1` a fresh atom), not the kernel's reach: at the loops' width every screen-pass claim is provable, and what
  differs is the price (milliseconds in `verdict`, 0.3 s in the every-input proof). That matches the parked `shr1` entry
  (219 of 219 oracle rules). It makes A_unp a prediction of which claims the cheap path misses, not of which are true,
  and the hard-negative shortage extends to the kernel's own label: among claims that pass the screen and width 4, none
  was refuted and none was unprovable at width 4. Not shown: width 8 or wider (the proof is at width 4, and width 6 is a
  test, not a proof).

*A key refined by counterexamples (2026-10-22; run `2026-10-22-key-refine`, 4.5 min, CPU 24% at launch; exe 9607129
plus `docs/runs/2026-10-22/patches/key_refine.patch`, reverted; script `docs/runs/2026-10-22/scripts/key_refine.sh`).*
The table's key learns its inputs from the merges it gets wrong. Each round builds the table to size 9 under the
current key and samples 20000 of the merges it proposes. It refutes them on 4096 random width-8 inputs, every width-4
input and the screen. For each refuted merge that the inputs added this round do not already separate, it adds one
refuting input to the key. It stops when a round's sample has no refuted merge. Then the held-out laws are normalised by
the final table, as in the two sections above, and its replacements are proved.

| starting key | rounds | final key (bytes per class) | classes (`lt`) | build | law meets, replacements |
|---|---|---|---|---|---|
| 8 tuples of 0s and 1s | 16 | 208 at width 8, 108 at width 4 (316) | 236109 (69902) | 1.5 s | as the exhaustive key: 3203, 0 suspect, all proved |
| plus 64 random | 19 | 262 at width 8, 114 at width 4 (376) | 236140 (69933) | 2.2 s | the same |
| exhaustive widths 3 and 4 | 3 | plus 4 at width 8 (4612) | 236160 (69957) | 12 s | the same |

- **A key of 316 inputs does what the exhaustive key's 4608 do here.** It meets the same laws through the same 3203
  replacements, all proved and kernel-checked (2820 by `add_tree_law`, 383 by `bitwise_law_k`). It is 15 times smaller
  per class, and its table builds about 7 times faster. After the first round, 759 of the 763 refuted merges from the
  0/1 key and all 391 from the 64-input key are `lt`, as the calibration above predicts: a wrong `lt` merge differs on
  rare inputs, so the key has to be told them.
- **The refinement took 52 s from the 0/1 key and 31 s from the 64-input key** (the rounds alone), mostly table builds.
  The exhaustive key needed 4 width-8 inputs for its wrong merges (`shl1` ones in the calibration above).
- **No key here is exact.** Stopping on a clean sample of 20000 bounds the rate of wrong merges to a few in 20000 (at
  95%), not to zero. The refined 0/1 key has 55 fewer `lt` classes than the refined exhaustive key, and the refined
  exhaustive key 4 fewer bit-vector classes than the refined random keys, so each still merges what another keeps
  apart. The refuter never
  tests width 3, so merges wrong only there go unseen. None of these merges was used by the laws (0 suspects). So a
  table's replacements still need their proofs, as everywhere else, and a failed proof is one more counterexample.

*`shr1` in the class table, its proofs over atoms, and a table's memory (2026-10-23; runs `2026-10-23-class-mem-shr1-b`,
75 s, CPU 17% at launch, and `2026-10-23-class-atoms-c`, 128 s, CPU 68% at launch; exes ddf1eba plus
`docs/runs/2026-10-23/patches/class_mem_shr1.patch` and 73724df plus `class_atoms.patch`, reverted; scripts
`class_mem_shr1.sh` and `class_atoms.sh` in `docs/runs/2026-10-23/scripts/`; the growth of repeated builds:
`2026-10-23-class-growth-c`; parse-first representatives: `2026-10-23-class-rep`; the allocator:
`2026-10-23-class-collect-b`; the screen memo in a sweep: `2026-10-23-screen-size`. Runs `-class-mem-shr1`, `-class-atoms` and
`-class-atoms-b` stopped on probe bugs: a pair over `add` sent to `bitwise_law_k`, a pair false over atoms sent to it
with a panicking check (the kernel refused it), and too many screen tries.)* The unmeasured risks of the class-table
spec (`docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md`). The probe above, with `shl1` and `shr1`
enumerated as unary operators (second operand `0`), refines a key from the 8 tuples of 0s and 1s, proves the final
sample's merges that contain `shr1`, normalises the held-out laws and proves their replacements, and writes the key; a
second process then builds the table once from that key and reports its commit (`K32GetProcessMemoryInfo`) and the
interner's node count. A replacement the machine cannot prove is retried over atoms (decision 3 of the spec): each
`shr1` node, outermost, becomes a fresh variable, the same on both sides; a pair that the screen refutes over atoms is
counted false there, and the rest go to `add_tree_law`, or to `bitwise_law_k` with the kernel deciding.

- **`shr1` grows the table by 45% and the key by 22%.** 16 rounds to a clean sample; the key is 262 inputs at width 8
  and 125 at width 4 (387, against 316 without `shr1`), and the table 341740 classes (95490 `lt`), 80112 of its 246250
  bit-vector representatives containing `shr1`. A fresh sample on the final key still refutes 4 `lt` merges, as
  expected of a key that is not exact.
- **Over x, y and z, most `shr1` replacements have no prover; over atoms, 89% of them do.** Of the 5265 sampled merges
  that contain `shr1` (none refuted), 666 are proved as they stand, all by `bitwise_law_k` (add-free). The other 4599
  mix `shr1` with `add` or `sub`, which `add_tree_law` cannot take: `Machine::parse` refuses `shr1` (a right shift reads
  a later bit position). Over atoms 4015 of them are proved, 582 are false and 2 have no proof (35 s for all 5265, about
  7 ms each, under load). So 584 (11%) stay unprovable. All 20 printed need what `shr1` means: a constant
  (`shr1(-1, 0)`, the top bit clear), a shift undone (`shl1(shr1(a, 0), 0) = and(a, -2)` in effect), or a comparison
  with a halved value (`lt(1, s) = lt(0, shr1(s, 0))`).
- **The held-out laws meet as before**: the same counts as the refined keys without `shr1` (15 of 15 residue laws,
  189-200 per set), through 3193 replacements, 0 suspect, 2804 proved by `add_tree_law`, 383 by `bitwise_law_k`. The 6
  without a proof are all one shape, `lt(sub(0, -1), s) = lt(0, shr1(s, 0))` with `s` a sum (`add(x, y)`,
  `sub(y, add(x, z))`, ...): both sides are the same size, and the `shr1` one is enumerated first (its left operand,
  `0`, is smaller), so it became the representative; the pair is false over atoms. The laws that met only through
  them are an upper bound. (Corrected 2026-10-23: this said the `shr1` side was a node smaller.)
- **One build commits 257 MB with large OS pages, peaks at about 215 MB without, and keeps about 95 MB** in a fresh
  process (1.6-1.9 s). Computed from counts, the structures it keeps are about 50 MB: 431494 interned nodes (56 B each before allocator overhead, about 30 MB), the interner's 1048576
  cells (8 MB) and the class map's 458752 slots (about 11 MB). The rest fits the value vectors of the build (387 B per
  bit-vector representative in two vectors inside a third, about 500 B with their headers, about 125 MB), dropped when the
  build returns while the commit stays at its peak. The probes run on mimalloc (`crates/church-bv/src/lib.rs`) with large
  OS pages allowed, which commit up front (65 MB at start) and are never returned. With them off, as a sweep's
  children run them (`MIMALLOC_ALLOW_LARGE_OS_PAGES=0`), a build peaks at 211-221 MB from 4 MB at start, and
  `mi_collect(true)` after it brings the commit to 95-98 MB (run `2026-10-23-class-collect-b`, 230bc3b plus
  `class_collect.patch`, script `class_collect.sh`). So mimalloc returns the freed values; about 90 MB stays, the kept
  structures and what mimalloc holds.
- **Repeated builds do not grow the commit; the refuter's screen memo does** (run `2026-10-23-class-growth-c`, 9730ff8
  plus `class_growth.patch` and `class_growth_1m.patch`, script `class_growth.sh`; 5 builds a process from the
  class-atoms-c key). The refinement's commit rose about 128 MB a round (1.4 GB after 16), while the interner grew only
  a few MB. Built 5 times with the same key and no refutation, the commit settles at 321 MB from the third build on; with
  4 inputs added a build it does the same, so a growing key is not the cause either. With the refutation loop it climbs
  to 769 MB, and the process-wide screen memo (`SCREENS`, never cleared) then holds 147027 vectors, 459 MB: 3264 B each,
  204 inputs of `u128` words for a width-8 term. Each round's sample screens 25-40 thousand new terms. The 448 MB above
  321 MB is that memo. Value blocks of 1 MB change nothing either (the allocator is mimalloc, with large OS pages, so
  nothing freed is returned in these probes; see the bullet above). A
  worker builds once and screens anyway, so the table adds no growth of its own. The screen memo stores `u128` at every
  width, 16 times what width 8 needs.
- **Representatives the prover can parse remove the 6 unproved held-out replacements** (run `2026-10-23-class-rep`,
  8ff0c06 plus `class_rep.patch`, script `class_rep.sh`; one build each from the class-atoms-c key, the last table
  kept though its fresh sample refutes 4 `lt` merges). A class's representative becomes its smallest member that
  `Machine::parse` takes, else its smallest. 796 of 341740 representatives move. Held-out laws: the same counts meet in
  every set, through 3187 replacements, all proved (2804 by `add_tree_law`, 383 by `bitwise_law_k`), against 6
  unproved of 3193 with the smallest member. The sampled `shr1` merges are not helped: 632 of 5243 unusable (629 false
  over atoms, 3 unproved) against 642 of 5272, since their own terms contain `shr1`. Those need a prover that knows
  what `shr1` means (`PARKED.md`).

*The class table as a module: the learned key, held-out proofs and a build's memory (2026-10-23; runs
`2026-10-23-class-key`, `-class-held`, `-class-commit`; scripts `class_key.sh`, `class_held.sh`, `class_commit.sh` in
`docs/runs/2026-10-23/scripts/`, the last on d5ea1aa plus `patches/class_commit.patch`; held-out laws in
`docs/runs/2026-10-23/fixtures/held`).* Plan `docs/superpowers/plans/2026-10-23-class-table-normal-form.md`, Tasks 1-4:
`crates/church-bv/src/classes.rs` builds the table once per process from a key baked into the test binary
(`crates/church-bv/data/class_key.txt`), with parse-first representatives and a verdict (bitwise, or a carry encoding over
`shr1` atoms) for each replacement it makes.
- **The key: 432 inputs in 26 rounds** (283 at width 8, 133 at width 4, 16 at width 3), against the probe's 387 in 16
  rounds. The refuter now also tries every width-3 input, which the probe never did ("A key refined by
  counterexamples"); its 16 width-3 inputs split merges wrong only at width 3, and the key's 45 extra inputs split the
  table into 341866 classes (95616 `lt`), 126 more than the probe's 341740. A build takes 1.7-2.1 s.
- **Every held-out replacement has a proof.** The laws meet as the probe's did (15 of 15 residue laws; 189-200 of 200
  in each family's size-11 and size-13 sets, all at sizes 7 and 9): 2174 of 2204 laws, through 3187 replacements, none
  unusable, their verdicts in 570 ms; the 2174 laws compile to kernel-checked proofs in 88 s (about 40 ms each, CPU 29%
  at launch).
- **A build commits 191 MB with large OS pages off, and `mi_collect(true)` returns it to 72 MB**; with them on it commits
  257 MB and returns nothing. So `Classes::get` now calls `mi_collect(true)` after the build (plan R9: kept when it
  frees at least 50 MB in a sweep child's setting, large pages off). The probe's 95-98 MB after collecting ("`shr1` in
  the class table ...") was on an older table and key; the numbers here are the module's.
- **The twin filter on the table** (plan Task 5; run `2026-10-23-ct-twins-gate-u`, arms acf1f24 and its Task 5 change,
  salts 1-5 of `cold:cmp3d`, untimed: `-Timed` refused for 90 minutes while another session's job kept CPU 2 busy, so
  wall and CPU are contended). `search::twin_key` makes each side's children canonical by the class table, replacing
  `ClassReps` (two-leaf classes, the family pool's subterms and a child of equal value). On the probe's fixture it finds
  251 twins and 710 trivial laws of 1050 extras, against `ClassReps`'s 443 and 409: fewer twins but more dropped (961
  against 852), since nodes the table merges below a root make laws trivial that were twins. M is 377 in both arms, equal
  in every one of the 15 loops, though no loop's rules are the same (the extras differ); L per scope (`GEN_LAWS`, before
  the filter) is unchanged, 4730-4868. Wall 83 s against 71 s, job CPU 656 s against 509 s, the largest `peakproc`
  528 MB against 603 MB (each B worker builds the table once).

*The class table in `prove_eq`: phase 1 (2026-10-23; plan docs/superpowers/plans/2026-10-23-class-table-normal-form.md,
Task 6; runs `2026-10-23-ct-phase1-restore` and `-ct-phase1-gate`, 9a2d456, salts of `cold:cmp3d`, untimed: another
session's job kept CPU 2 busy, so wall and CPU are contended, though arm A's job CPU, 508 s, matches the same build's
509 s in `-ct-twins-gate-u`).* After the per-position step, `prove_eq` normalizes both sides by the table's proved
replacements and closes the pair if they meet (`ABLATE=classes` turns it off).
- **The switch restores the old answers**: the build with `ABLATE=classes` in its `.env` against the build before it,
  salt 1: M 76 and 76, rules the same in 3 of 3 loops.
- **M falls 38%: 377 to 233** (A the build ablated, B with phase 1; salts 1-5), lower in every one of the 15 loops (by
  3-14), every rule file different. Laws joined fall from 851 to 533 and the join's reached terms barely move (46190 to
  45716): the table closes pairs the join closed before, and many the join and the machine did not.
- **Replacements per batch** (`m.tsv`'s ninth column): 8-50 in B, 1068 in all over 45 batches; 0 in A. An over-count:
  until the final review's fix it also counted the steps of pairs the table left open, which no proof used
  (`classes::steps_of_a_pair_left_open_are_not_counted`). Counted right (run `2026-10-23-ct-fix-gate-u`, same rules
  and M): 1-29 per batch, 542 in all, about half. 5 distinct
  replacements were met with no proof (`CLASS_UNUSABLE`), all over large `add`/`sub`/`shl1` terms, so normalizing stopped
  short there.
- **Cost: job CPU +29% (508 s to 655 s), wall 71 s to 96 s, the largest `peakproc` 577 MB to 684 MB (+107 MB).** Each
  B process builds the table once (15 builds, 1.6-1.7 s, 24 s of the 147 s added; the 5 in A are the sweep's own, for the
  twin filter). The rest is phase 1's normalizing and proofs, and different rules and laws mined; this run does not
  separate them. This was past the plan's 25% stop; with `rep` memoized (below) it is under it (`PARKED.md`, "Phase 1's
  CPU cost").
- **Where the added CPU goes** (run `2026-10-23-phase1-prof`, samply over salt 1's whole sweep, both arms, 83f698b plus
  `docs/runs/2026-10-23/patches/phase1_prof.patch`, script `phase1_prof.sh`, CPU 5% at launch; frames in
  `docs/runs/2026-10-23/rows/2026-10-23-phase1-prof.txt`; busy samples, not weighted by CPU). Both arms reproduce the
  gate's salt 1 (M 49 and 76). Busy samples 105058 off, 119370 on (+14312, +13.6%; the gate's salt 1 +15%).
  `prove_eq` adds 7759 net: the table's lookups cost about 7000 (`class_hash` 2984, code with no `church_bv` frame
  below `prove_eq` 3581, reallocation and the memo's lock 835), and the machine work inside `prove_eq` falls by 3281
  (`join_or_machine` 4832 to 1551). The workers' builds (`Classes::get`) are 4177, about 29%; in the kernel-check task
  the build is all the samples it has. The rest, about 2400 net, is the different work the different rules bring (the
  rewriter +3790). So hashing values for lookups and building the table per worker are most of the cost.
- **`rep` memoized: job CPU +22%** (run `2026-10-23-ct-memo-gate`, 5565cfa, both arms that build, A with
  `ABLATE=classes`; untimed, the other session's job still on CPU 2, CPU 5% at launch). `Classes::rep` keeps its
  answer per term under the value memos' lock, so a term's values are gathered and hashed once per process. M is
  unchanged, 377 to 233; job CPU 462 s to 565 s (+22%, was +29%), wall 64 s to 83 s; the largest `peakproc` 568 MB to
  701 MB (+133 MB, was +107 MB: the memo's map, or noise). Per salt the change in CPU spans -5% (salt 2) to +78%
  (salt 3). Not profiled again; the profile's other large item was the builds per worker (`PARKED.md`, "Cache the
  built class table").
- **What a build spends (throwaway probe, 644e37e, reverted; untimed, single thread).** A build takes 1.39-1.48 s and
  hashes 989535 candidates (341866 classes, 647669 merges). Hashing them all with `class_hash` (two SipHash passes over
  432 bytes) takes about 150 ms; two foldhash passes take 31 ms, so a faster hash saves about 8% of a build, about 1.7 s
  of a five-salt gate's 15 builds. The values are most of it: `zip`'s per-element calls through `OP_INFO[o].word` (with
  each element's own width mask) and a fresh vector per candidate take about 905 ms, 65%. The rest, about 350 ms, is the
  map, `Term::op` and `Machine::parse`.
- **The build zips a width at a time: a build 0.58-0.65 s, job CPU +19%, timed** (08adb24; run `2026-10-23-ct-zip-gate`,
  `-Timed`, quiet: total 6.3%, CPUs 8 and 9 0.4%). The build calls `rewrite::zip_op` (the operator dispatch `ValueMemo::fill`
  had, now shared) once per key width with that width's mask, into one reused buffer copied out only for a new class.
  `the_full_table_is_pinned` holds the table to its counts and a fingerprint of every pair, unchanged. A build went from
  1.39-1.48 s to 0.58-0.65 s. Gate, A with `ABLATE=classes`: M 377 to 233; job CPU 459 s to 545 s (+19%), wall 60 s to
  74 s; the largest `peakproc` 626 MB to 695 MB. Per salt the change in CPU spans -10% (salt 2) to +73% (salt 3). The
  phase-1 gates before this one were untimed.
- **foldhash for `class_hash`: no faster in the build (negative; patch `docs/runs/2026-10-23/patches/class_hash_foldhash.patch`,
  reverted).** On 1fe8f57, two foldhash passes on fixed seeds (`foldhash` 0.2 as a dev-dependency, already in the lock
  file through hashbrown, which seeds it per process and does not expose fixed seeds) left the table unchanged
  (`the_full_table_is_pinned`, whose fingerprint now covers representatives only) and the build where it was: alternating
  five runs each, SipHash 604-721 ms, foldhash 594-624 ms. The isolated loop's 150 ms to 31 ms does not show in the
  build, likely because hashing overlaps the map's cache misses. SipHash stays.
- **Salt 3's +73% is the miner's lookahead, not the table** (run `2026-10-23-phase1-prof-s3`, samply over salt 3's whole
  sweep, both arms, 47826fa plus `docs/runs/2026-10-23/patches/sweep_prof_salt.patch`, script `phase1_prof_salt.sh`;
  frames and the miner's counts in `docs/runs/2026-10-23/rows/2026-10-23-phase1-prof-s3.txt`). Both arms reproduce the
  gate's salt 3 (M 73 and 41). Busy samples 81693 off, 142290 on (+74%). The table's own work is small: `prove_eq`
  +4216 (a build 1423, the verdict memo's lock 427), the kernel-check task's build 1565. The rest is the miner scoring
  more: `score_laws` +44428, inside it the join +23754 and the rewriter +14727. In loops 2 and 3 the main mine meets a
  winner whose rival gains more in its round 3 times each (none off, none in loop 1), and each such choice finishes both
  greedy paths (`play`'s lookahead, "The cold loss is a greedy path loss"): 268 and 209 scoring rounds for 74 and 66
  rule-set evaluations, against 60 and 60 for 59 each off; 2.7x the candidates scored over the three loops (98685
  against 36634). So the table changes which rules the mine meets, and on this salt that switches the lookahead on;
  phase 1's own cost here is about a tenth of the added samples.
- **The mines' rounds follow the CPU on every salt** (the zip gate's logs, `2026-10-23-ct-zip-gate`, re-read; `salts_ab.sh`
  now prints mine rounds and lookahead decisions per loop and per arm, over every mine's log). Rounds A to B and job CPU:
  salt 1 382 to 440 (+10% CPU), salt 2 353 to 362 (-10%), salt 3 187 to 543 (+73%), salt 4 196 to 273 (+22%), salt 5
  190 to 313 (+19%); 1308 to 1931 in all (+48%), lookahead decisions 7 to 18. So most of phase 1's +19% is the miner
  playing more rounds on the rules the table lets it meet, not the table's own lookups; a gate comparing phase-1 changes
  should read rounds beside CPU.
- **Displaced representatives stay inside stored ones** (throwaway probe, patch
  `docs/runs/2026-10-23/patches/probe_rep_fixpoints.patch`, on 299a68d, reverted; final review M1). Of the 798
  displacements 69 are bit-vector classes (the rest `lt`, which no operator takes). 903 of 341866 stored representatives
  (186 of them `lt`) hold a proper subterm the table itself replaces, over 42 distinct replacements; the 8 printed are
  each a displaced `shl1(…shr1(…, 0)…, 0)` term whose successor is a larger `add`/`and(…, shl1(-1, 0))` form, e.g. `or(x, shl1(xor(x,
  shr1(y, 0)), 0))` holds `shl1(xor(x, shr1(y, 0)), 0)`, which steps to `xor(add(x, x), and(y, shl1(-1, 0)))`. So spec
  §5's premise that a representative is a fixpoint failed for 0.26% of the table (phase 1 was unaffected: it stops where
  no verdict exists). **Fixed:** after the build, `Classes::build` puts each displaced representative's successor into
  every stored representative holding it (substituting at displacement could not work: the successor is larger, so
  terms already built at smaller sizes could not take it). `representatives_are_fixpoints_below_the_root` (903 before,
  none after); the table's counts unchanged, its pin re-taken; the held-out laws unchanged (2174 of 2204 met, 3187
  replacements, all proved: they never reached the 903). The gate is unchanged too (run `2026-10-23-ct-fix-gate-u`,
  a678745, untimed after two `-Timed` refusals on a busy machine): M 377 to 233, mine rounds 1308 to 1931, and all 30
  rule files the same as the zip gate's, so the 903 never reached a mined law either; the `classes` column, now counted
  right, is 542 (above, "Replacements per batch").
- **Phase 2 leaves the miner nothing to learn on the gate** (throwaway spike, patch
  `docs/runs/2026-10-23/patches/phase2_spike.patch`, on e38e94b, reverted; run `2026-10-23-phase2-spike`, `-Timed`,
  quiet). The spike looks up every node in `rewrite_uncached` after its children: a node the table knows is final, either
  its own representative or the verdict-gated step to it, and rules run only on unknown nodes. Against A
  (`ABLATE=classes`, so no table at all): M 377 to 0; stragglers before mining 2314 to 229; mine rounds 1308 to 194,
  lookaheads 7 to 0; job CPU 451 to 26 s, wall 58 to 10 s. Every served law is proved in both arms (4500), all of them
  free in B (4123 in A), with 5323 table steps and no join. The lookup memo stayed under 50000 terms and new verdict
  pairs under 2000 per process; no `CLASS_UNUSABLE`; largest peakproc 609 MB (A 555). So on the gate's laws, nearly all within
  inside the table's domain, the table subsumes the mined rules, and the gate stops measuring mining: phase 2 needs
  laws past the table's domain (above SIZE 9) for the miner to have work. Five rewrite tests built on rule cycles
  failed under the spike, since the table settles their terms first.
- **The table leaves 2-12% of grown laws open** (throwaway probe `search::open_law_counts`, patch
  `docs/runs/2026-10-23/patches/open_law_counts.patch`, script `docs/runs/2026-10-23/scripts/open_laws.sh`, on c201b40,
  reverted; run `2026-10-23-open-laws`, salt 1, 9 s). Each family's pool grown 1-3 times (one leaf into an operator over
  two leaves, padding dropped, about 20000 terms per level), laws as `grammar_laws` makes them, up to 300 per (level,
  size) normalized by `Classes::normalize`; open when the normal forms differ. No law of size 9 or less is open, at any
  level. Above it, the table still settles 88-98%: through `rep` on terms larger than its SIZE, verdict-gated. Estimated
  open laws (open share times the bucket's laws), growth up to 2 / up to 3 levels: add3 360 / 856, sbo3 93 / 377, mix3
  115 / 307, cmp3d 640 / 1767; largest buckets size 13 (add3 478, cmp3d level 2 459) and cmp3d's size 15 (1044 of 8467).
  So a stream of open laws filters about 20 grown laws per law kept, and only add3 and cmp3d reach a few hundred
  within two growths.
- **Seeded from the table instead of a family** (same probe with a `table` seed, patch
  `docs/runs/2026-10-23/patches/open_law_counts_table.patch` (adds `Classes::reps` and unary `shr1` growth), reverted;
  run `2026-10-23-open-laws-table`, 11 s). Seeds: 20149 of the 341866 representatives drawn by salt 1, grown over all
  seven operators. Laws are fewer but more often open: 564 / 939 / 876 laws at levels 1 / 2 / 3 (families: 4600-15000),
  of which 20-24% open (families 2-12%): about 129 open laws within one growth, 314 within two, 492 within three, at
  sizes 11, 13 and 15 (a seed is mostly size 9, each growth adds 2). Distinct representatives rarely meet at width 4, so
  a law needs a grown term to land in a seed's group; the count follows the growth budget (`GEN_TERMS`), not the seeds.
  None of the open laws, here or in the families' rerun (the same counts as above), differs on 4096 random width-8
  inputs, so width-4 grouping made no false open law at this budget.
- **A larger growth budget gives fewer open laws per term** (same probe with the budget a knob; run
  `2026-10-23-open-laws-budget`, table seed, budgets 20000 / 40000 / 80000 terms per level). Laws grow faster than
  the budget (level 1: 564 / 1374 / 3362), but the open share falls (level 1 size 11: 24% / 15% / 6%), so the open laws
  within two growths are 314 / 435 / 589 and within three 492 / 834 / 1180: ×4 budget gives ×1.9, not the ×4 the seed
  count argument predicted (falsified). The new laws are mostly ones the table settles. False open laws appear at the
  larger budgets (2 of 60 open in one bucket at 40000, 1 of 26 at 80000; excluded from the counts), so a stream must
  check open laws at width 8 before using them.
- **More seeds give fewer open laws** (same probe; run `2026-10-23-open-laws-seeds`, budget 20000, 20149 / 80513 /
  341866 seeds, the last every representative). Laws grow (level 1: 564 / 849 / 2062) but the open share falls (level
  1 size 11: 24% / 15% / 3%): open laws within two growths 314 / 295 / 225, within three 492 / 448 / 327. A law pairs a
  grown term with its width-4 group's first member, a seed when the group has one; the more seeds, the likelier that
  seed is the grown term's own representative, which the table steps to. False open laws rise with the seeds (6 of 61
  open across all representatives' buckets, 4 of 24 in one). So neither lever scales the table-seeded stream past a few
  hundred open laws per salt: an open law needs a side the table does not reach, and pairing with a seed supplies the
  other side from inside the table.
- **Pairing grown terms with each other changes nothing** (same probe, `OL_PAIR=grown`: seeds left out of the
  grouping, so both sides of every law are grown; run `2026-10-23-open-laws-grown`, 20149 seeds). Open laws within two
  growths 292 / 678 at budgets 20000 / 80000 (seed pairing 314 / 589), within three 464 / 1165 (492 / 1180). So the
  explanation in the bullet above is falsified: what caps the stream is how many grown terms fall in classes the table
  does not reach, not which member a law pairs them with. The table-seeded stream gives about 1170 open laws per
  salt at budget 80000 within three growths, 40% of them (470) of size 15.
- **What the open laws are** (same probe, each open law that holds on 4096 random width-8 inputs classified, with
  a throwaway `Classes::class_of`; run `2026-10-23-open-laws-cap`, budget 80000, up to 2000 laws per bucket, seeds:
  the table's 20149, cmp3d, add3). Each side's normal form is `unknown` (its class is not in the table: a function no
  term of size 9 or less computes), `refused` (the class is stored but the verdict refused the step to it) or `rep` (it
  is its class's representative).
  - cmp3d: 931 of 932 open laws are unknown+unknown, over 781 distinct functions. add3: all 627, over 560 functions.
    So a family's open laws are new functions, nearly one law per function.
  - Table seed: of 581, 364 refused+rep and 35 refused+refused: the table knows the function but the step is refused
    (laws the table would close if its proof did); only 151 are unknown+unknown. 31 are rep+rep: two stored classes, so
    the key separates the sides at some width from 1 to 8 although width 4 and 4096 width-8 inputs agree, i.e. false
    laws that a width-8 sample misses. 581 laws hold 363 functions, the top two 61 and 43 (one-bit `lt` results).
  - Operators of the families' open laws: cmp3d `lt` over add, sub with xor (321) or `shl1` (192) or both (158); add3
    add with xor and sub (168), with or (103), and (72), both (72). (The probe's printed names are off by one past
    `sub`: its `shr1` is `shl1`, its `?` is `shr1`.)
  - So the cap is how many grown terms compute functions beyond size 9. Arithmetic-heavy family pools reach them;
    growth from the table's representatives mostly lands in functions the table has, where an open law is a refused
    verdict or a false law. A stream for the miner wants the `unknown` signal (the class is not stored), not only
    "open", and a check over the key's widths, not a width-8 sample.
- **Growing from beyond the table does not help the table seed** (same probe, `OL_FRONTIER=1`: each level grows only
  the previous level's terms whose class the table does not store; run `2026-10-23-open-laws-frontier`, budget 80000,
  2000 laws per bucket). Most grown terms are already beyond the table (table seed: 60055 of 79606 at level 1, 76265
  of 80369 at level 3 with the frontier; cmp3d: 12856 of 73417 at level 1), so reaching new functions is not the cap.
  Pairing is: the table seed's 80000 terms per level make 2967-4305 laws, cmp3d's 31137-47874, so its open laws are
  ten times as many (cmp3d, within three growths, estimated from 2000 per bucket: about 11600 without the frontier,
  15300 with; the table seed about 1100 without and 760 with, unknown+unknown 151 / 177 of 581 / 529 classified). The 300-law
  samples above at budget 20000 had put cmp3d at 1767, so the families' streams do scale with the budget; only the
  table seed's does not. A family pool is a few operators with many syntactic variants of each function (reassociation
  inside `lt`), so its grown terms keep meeting each other; random representatives over seven operators grow apart.
- **An operator set over the table matches the cmp3d pool** (same probe, `OL_OPS`: the seeds are every representative
  whose operators lie in a set; run `2026-10-23-open-laws-opsets`, budget 80000, 2000 laws per bucket). cmp3d's set
  {add, sub, shl1, lt}: 6448 seeds, about 13950 open laws within three growths (the cmp3d pool about 11600), 1345 of
  1347 classified unknown+unknown over 1194 functions; 32 open laws refuted at width 8 (excluded), none rep+rep. add3's
  set {add, and, or, xor, sub}: 133420 seeds but about 655 open laws (all unknown+unknown, 154 functions), below the
  add3 pool's 856 at budget 20000. So the narrow arithmetic set pairs as well as the hand pool without it, while a set of
  five operators is broad enough that grown terms grow apart, as with all seven: what pairs is a small operator set,
  not a hand-written pool.
- **Two operators pair best; `lt` and breadth hurt** (run `2026-10-23-open-laws-sweep`, `scripts/opset_sweep.sh`: every
  set of 2-4 of the seven bit-vector operators, with and without `lt`, 182 sets, budget 20000, two growths, 300 laws
  per bucket; open laws exclude the 485 of 15782 sampled that width 8 refutes). Means by set size: two operators about
  1410 open laws over 93 functions (1094 seeds), three 902 over 103, four 365 over 62; `lt` lowers each (863/621/291
  open) and raises functions in only 8 of 91 sets, its open laws mostly refused verdicts. Best by functions: add with
  one of shr1, and, or, shl1 (263-273; add,shr1 4624 open laws), and add,and,shr1 (274), against 314 open laws for the
  whole table and 640 for the cmp3d pool at the same budget. Sets with many open laws but few functions are refused
  verdicts (and,shr1,lt: 3126 open, 217 of 260 refused, 36 functions); sets of bitwise operators alone or of shl1,shr1
  give none. Across all sets 11555 of 15297 classified are unknown+unknown. The function counts here are of the sampled
  laws only (300 per bucket), so they cap near the sample: counted over every law (next bullet, budget 20000 each), add,shr1 has 1011
  functions, add,and 1550 and add,or 1564.
- **Rotating over every operator pair beats the best pair** (run `2026-10-23-open-laws-mix`, `scripts/mix_streams.sh`,
  every law checked rather than sampled, two growths). The 21 pairs of the seven operators as separate table-seeded
  streams at budget 20000 each: 8847 distinct functions over 28927 open laws, against 8966 summed over the streams, so
  they overlap by about 1%. add,shr1 alone at the same total budget (420000): 2348 functions over 61196 open laws, about
  26 laws per function against 3.3. So each pair finds functions of its own, and one pair's larger budget mostly
  restates the same functions. Pairs vary: add with and/or about 1550 each; and,or and shl1,shr1 none; and,xor and
  or,xor 7 and 17.
- **Triples match pairs per grown term** (run `2026-10-23-open-laws-triples`, `scripts/set_sizes.sh`, same probe). The
  35 triples at the pairs' total budget (12000 each, 420000 in all): 8962 distinct functions against the pairs' 8847.
  At 20000 each (700000): 16547 functions over 32262 open laws, every triple some (18 to 1181). Pairs and triples
  together at 20000 each: 22292, against 25394 for the two summed, so a triple stream mostly adds functions the pairs
  miss. About 20-24 new functions per 1000 grown terms for pairs, triples or both, and the triples' yield rose faster
  than their budget (x1.67 budget, x1.85 functions). So the set size is not what matters; rotating over small operator
  sets is.

