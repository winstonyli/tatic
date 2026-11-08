## Proposers and ranking

### Experiment 1, kernel side (2026-10-10)
`search::classify_proposals` gives each proposed `lhs = rhs` line a verdict (unparsed, trivial, refuted, duplicate, memorised, known or
novel, each cheap or hard); the ignored test `proposal_yield` samples a proposer and prints a `YIELD` line (env documented on the test). Both were
deleted with the families (b63d5ed, 093ffc1); read them with `git show b63d5ed^:tests/church_bv/search.rs`.
Baselines, 2000 samples, shuffle salt 1, default 250-law training window, no mined rules, one run each:

| family | proposer | unparsed | refuted | trivial/dup/memorised | true and new to the stream |
|---|---|---|---|---|---|
| add3 | uniform pool pairs | 0 | 1940 | 1 | 59 cheap |
| add3 | char 8-gram | 1517 | 472 | 11 | 0 |
| sbo3 | uniform pool pairs | 0 | 1960 | 0 | 1 known cheap, 38 cheap + 1 hard outside the family |
| sbo3 | char 8-gram | 1883 | 117 | 0 | 0 |
| cmp3d | uniform pool pairs | 0 | 1945 | 0 | 51 cheap + 4 hard outside the family |
| cmp3d | char 8-gram | 1983 | 17 | 0 | 0 |

Reading: random pool pairs are about 97% false (2-3% true); the n-gram mostly does not even parse (76-99%) and yields no true new
law, so a proposer must clearly beat both to be worth wiring in. "Outside the family" means true laws that the family's windowed
sequence omits (for example fewer than three variables); `known` counts only the family's own laws. With no rules installed the cheap
and hard split reflects only the built-in rules. With a mined library installed (4000 pool samples, salt 1; none / family's own 8-rule library / 25-rule u3 library), the hard
true laws were add3 1/0/0, sbo3 2/1/1, cmp3d 5/4/2. Uniform pairs almost never hit the laws that M counts: the true ones are nearly
all cheap with no rules at all. A proposer is worth something to the miner only if it targets hard laws (idea 2 below).

### Difficulty band (2026-10-10)
`classify_proposals` now returns a `Cost` for each true, unmemorised law (machine proofs used, rule steps of the 200-step budget,
proved or not). The band is fixed: `Cost::hard` = still needs a machine proof, the laws M counts. `proposal_yield` prints a `BAND` line
and `BAND_OUT` writes the hard laws as a stream for the loop. `PROPOSER=stream` replays the family's own hash-ordered sequence from
`YIELD_SKIP`, the baseline experiment 2 compares against. Check, u3 library (salt 1), 300 held-out laws from skip 1000: the stream's
band is 30 (sbo3) and 9 (cmp3d), exactly M from `rule_set_kernel_check`. The pool proposer's band over the same 300 samples is 0 and 1.
The hard stream laws used 57 and 13 machine proofs with median rule steps 3 and 1, so the machine-proof count is the useful grade; rule
steps barely separate them. The stream also has 4-12 laws per 300 whose sides print identically, and 7-18 printed duplicates. All are
cheap, so M is unaffected.

### Mutation proposer and mining from the band (2026-10-10)
Setup: cold (no rules), shuffle salt 1, `RULEMINER_FAST`, 8-round cap, one run per cell. Seeds = the hard laws of the first 300 stream
laws (sbo3 75, cmp3d 100). `PROPOSER=mutate` (`MUTATE_SEEDS`, `MUTATE_KIND`) mutates them: `subst` (a variable becomes a small term on
both sides) and `wrap` (both sides under one operator with a small term) are true by construction; `edit` (one node of one side
replaced) mostly is not. The band (hard laws) per 1000 mutants:

| family | subst | wrap | edit | mix | pool pairs (per 1000, earlier) |
|---|---|---|---|---|---|
| sbo3 | 556 | 846 | 78 (895 refuted) | 534 | ~0.5 |
| cmp3d | 674 | none (every law is `lt`-rooted) | 75 (902 refuted) | 247 of 667 | ~1 |

So a proposer aimed at hard laws fills the band easily. But do the band laws teach better rules? `RULEMINER_LAWFILE` mines from a file.
Held-out M (300 laws, skip 2000 sbo3 / 5000 cmp3d; lower is better), each library 8 rules:

| mined from | sbo3 | cmp3d | mining time sbo3 / cmp3d |
|---|---|---|---|
| no rules | 94 | 109 | |
| stream, 300 laws (75 / 102 hard) | 19 | 27 | 47 s / 197 s |
| band, 300 hard laws from the first 1500 | 22 | 42 | 79 s / 306 s |
| mutants, 300 / 247 hard | 88 | 80 | 195 s / 253 s |
| stream + band | 22 | 44 | 105 s / 269 s |
| stream + mutants | 87 | 82 | 226 s / 261 s |

Reading: being hard is not enough. Hard mutants teach rules that barely transfer back to the family (M 80-88 vs 19-27), because they
are hard for reasons of their own (context, instances) rather than for the family's. Mining only from the stream's own hard laws is
no better than mining from the stream, and on cmp3d it is worse (42 vs 27, one run). The guard is not the cause: adding the stream's
cheap laws, which feed `RULEMINER_GUARD`, left it at 44. The 8-round cap binds in every cell, so more hard laws cannot buy more rules
here. For the cycle: the proposer's reward needs a transfer term (does a rule mined from its proposals lower M on the target
distribution), not difficulty alone. Experiment 2 has to measure that directly.

Salts 2 and 3 (stream vs band only, same setup), held-out M none / stream / band: sbo3 94 / 21 / 24 and 77 / 16 / 16; cmp3d 123 / 38 /
44 and 101 / 35 / 38. Mining from the band is never better than mining from the stream, and is usually within a few laws; salt 1's
cmp3d gap (27 vs 42) is the largest of the three.

**Transfer score.** `scripts/transfer_score.sh` (header documents it) mines rules from a law file and prints
`TRANSFER ... M_before M_after gain` on a held-out window of the target family: the batch-level reward a proposer needs. Check: the
salt-1 sbo3 stream file gives 94 -> 19 (gain 75), matching the table above. It costs one mine per batch (about 1-5 min FAST), so it
grades batches, not single proposals. Since 2026-10-11 it mines on serving's 200-step budget (it had kept the miner's old 40) with
no round cap; on a 30-law salt-1 sbo3 file both budgets mine the same 16 rules (held-out M 92 -> 61).

**Per-proposal credit.** `search::proposal_credit` (report test `proposal_credit_report`, env on the test). A rule's held-out gain is how
many more held-out laws are hard without it. A proposal *uses* a rule when it is cheap with the library but hard without that rule.
Each rule's gain is split evenly over its users. The cost is two passes per rule over the held-out window and the batch, seconds in
all, with no re-mining. Salt-1 libraries from the band-mining run, held-out windows as there (after the pool dedup, so M differs a
little from the tables above):

| library mined from | held-out M | sum of rule gains | proposals credited | rules with gain <= 0 |
|---|---|---|---|---|
| sbo3 stream | 92 -> 21 | 104 | 70 of 300 | 1 |
| sbo3 band | 92 -> 22 | 86 | 219 of 300 | 2 |
| sbo3 mutants | 92 -> 87 | 4 | 45 of 300 | 3 (one at -1) |
| cmp3d stream | 118 -> 44 | 82 | 83 of 300 | 1 (at -8) |
| cmp3d band | 118 -> 44 | 86 | 198 of 300 | 0 |
| cmp3d mutants | 118 -> 84 | 34 | 91 of 247 | 1 |

Reading: the credit separates useful proposals from useless ones within a batch. Mutants that led to non-transferring rules earn
about nothing, and the stream's credit concentrates on about a quarter of the laws. Ablation gains overlap: their sum exceeds the
batch gain (104 vs 71) because rules substitute for each other, so credit is a ranking signal, not an additive budget. A rule can
hurt held-out laws (cmp3d stream, gain -8), so credit can be negative, which is the signal to drop that rule. Every rule here had at
least one user, so all gain was attributed. Not yet used to train anything.

### Ranking candidates, or mining on more laws (2026-10-17)

*Oracle headroom for a ranker (probe, reverted, 2026-10-17).* The proposer's target is ranking (top of this note), so first:
how much could any reordering of a round's candidates gain? Each mine of a cold loop (batch r) gets the laws of the batch served
next (r + 1). On the main path, a round's alternatives are the rival, the winner and the next k - 1 proved candidates by gain
(scoring goes down to the k-th best gain). Each is finished greedily, and the one whose finished set leaves the fewest laws of
the next batch without a machine-free proof is kept (its M, counted as `rule_set_kernel_check` with `CHECK_FAST` counts it).
Ties go to the earlier alternative, so the plain choice stands unless the next batch says otherwise. The predicted M matched
the served M in all 117 mines with a lookahead. M of the mined batches (1 and 2); batch 0 is served with no rules (331 and
322 at salts 1 and 2):

| k | salt 1 | salt 2 | both | cmp3d | add3 | sbo3 | cold stage |
|---|---|---|---|---|---|---|---|
| plain miner | 120 | 128 | 248 | 116 | 70 | 62 | 6 s |
| 1 (rival or winner) | 118 | 120 | 238 | 116 | 59 | 63 | 6-7 s |
| 3 | 93 | 107 | 200 | 111 | 36 | 53 | 9 s |
| 5 | 87 | 100 | 187 | 104 | 34 | 49 | 12-13 s |
| 10 | 87 | 101 | 188 | 105 | 34 | 49 | 17-18 s |

The plain rows reproduce the cold totals above (451 and 450). What it shows:
- **There is headroom, mostly beyond the runner-up.** A quarter of the mined batches' M (248 to 187). Choosing between rival
  and winner alone gets 10 of the 61. It is largest on add3 (70 to 34) and smallest on cmp3d (116 to 104).
- **It is concentrated.** At k = 5 the choice differed from the greedy one in 11 of 136 rounds (salt 1) and 13 of 127 (salt 2).
  The kept alternatives were spread over positions 1-4, and at k = 10 a few came from positions 6-10.
- **It is not reachable as tried so far.** A narrower move (rival, winner, runner-up) valued on in-sample folds tied
  ("Runners-up chosen held out"). A
  ranker has to predict the next batch's value from what it sees now, from about a dozen positive rounds per salt.
- **It is not a strict bound.** It looks one round ahead with greedy finishes, so a ranker that changes several rounds
  together could in principle do better. It also uses the batch it is scored on.

Each run is the whole cold stage (`SWEEP=cold`, salts 1 and 2), run two at a time at BelowNormal with affinity FFF. CPU was at
18% before the runs, and Defender RTP was False. Patch: `docs/runs/2026-10-12/patches/oracle_headroom_probe.patch` (against
9c601c3; `ORACLE_K=<k>` in the sweep's environment). Rows: `docs/runs/2026-10-12/rows/oracle_headroom/`.

*Can the miner see the headroom? (negative, 2026-10-17).* The same probe at k = 5 over salts 1-10, logging one row per
alternative (`ORACLEROW`: round, position, gain, in-sample finished value, next-batch M, sizes, variables, rule). The headroom
holds on every salt: mined-batch M 1169 to 925 (-21%; per salt 120/87, 128/100, 136/115, 96/86, 98/83, 126/94, 119/90,
124/97, 85/68, 137/105). The oracle switched in 127 of 1334 rounds, spread over the families (cmp3d 51, sbo3 40, add3 36).
Nothing the miner sees predicts those rounds (scripts `an1.awk`-`an4.awk` beside the rows):
- **In-sample finished value is worse than no signal.** Picking by it switches 186 rounds and agrees with the oracle on 38.
  Summed over rounds, it makes the next batch's M 132 worse (one round ahead each; the oracle's own choices sum to 352 better).
  This is the in-sample lookahead's loss again ("Lookahead over runners-up too").
- **Round gain never switches.** The first alternative already has the largest gain.
- **Given that a round should switch, no feature finds the alternative.** In the 127 switched rounds, a random alternative is
  a best one 30% of the time. Taking the top by each feature: in-sample value 38%, smaller right side 31%, fewer variables
  31%, gain 27%, smaller left side 28%; within noise of chance (about ±4 points).
- **A margin gate does not replicate.** Switching only when the in-sample value beats the greedy choice by 2 or more
  stragglers looked useful over all salts (net M -40), but it is -44 on salts 1-5 and +4 on salts 6-10.

What the oracle knows that the miner doesn't is the next batch. So a ranker's input has to say something about laws not yet
seen, not just the mined batch. Same runs as above (two at a time, 9-13 s per oracle run). The patch above includes the row
logging. Rows: `features_k5_s1-10.tsv.gz`, `salts_m_k<k>_s<salt>.tsv`.

**More laws beat any ranking (2026-10-17).** The same probe, valuing alternatives on a proxy instead of the next batch. The
proxy is laws from phase p + 3 of the same stream; cold loops serve only phases 1-3, so no proxy law is ever served.
`matched` is phase p + 3's window at the next batch's position (100 laws). `wide` is that phase's first 300 laws (fewer
where the phase is shorter: add3's has about 200). Then a control that does no ranking: the plain miner mining on its batch
plus the same proxy laws. Mined-batch M over salts 1-10:

| arm | M | cmp3d | add3 | sbo3 |
|---|---|---|---|---|
| plain miner | 1169 | 550 | 282 | 337 |
| proxy-ranked, matched (100 laws) | 1037 | 501 | 232 | 304 |
| proxy-ranked, wide (300 laws) | 973 | 454 | 223 | 296 |
| oracle-ranked (the next batch) | 925 | 455 | 194 | 276 |
| plain miner on batch + 300 proxy laws | **479** | 219 | 84 | 176 |

Batch 0, served before any mine, is 3211 in every arm.
- **A proxy does most of the oracle's work.** The wide proxy recovers 80% of the oracle's gain (1169 to 973 against 925) and
  is lower than plain on every salt. When it switches (184 of 1388 rounds), the true next batch is better in 92 rounds,
  worse in 17 and the same in 75. So the ranking signal is how a set generalizes to unseen laws of the stream, and a
  sample of the stream measures it. No learned model is needed for that.
- **Just mining on those laws is far better.** The control more than halves M (1169 to 479, -59%), lower on every salt and
  in every family's total: almost three times the oracle's gain. A reading: the miner is short of laws, not of good
  choices; a batch of 100 underdetermines the rules, and ranking among its candidates is the smaller lever.
- **What this means for the proposer.** The stream's unserved phases stand in for laws the system could generate itself
  (the 5-node enumeration yields every true law of that size). The lever is which, and how many, laws to mine on. That is
  the "ranking which laws" half of target (b), not ranking candidate rules. Not yet measured: whether proxy ranking adds
  anything on top of the extra laws.

Same machine conditions as above. Patch (now with `ORACLE_PROXY=matched|wide`, `ORACLE_TRUEFILE` logging and the
`MINE_EXTRA` control) as above. Rows: `salts_p_<proxy>_s<salt>.tsv`, `salts_c_extra_s<salt>.tsv`,
`features_wide_proxy_s1-10.tsv.gz` (column 16 is minus the true next-batch M).

*How many extra laws (2026-10-17).* `MINE_EXTRA=<n>`: each cold-loop mine adds the first n laws of the phases no cold loop
serves. It takes phase p + 3 first, then the next phases in order, skipping 1-3. `all` takes every such law: 813 for add3,
1913 for sbo3, 4871 for cmp3d. The plain miner otherwise. Mined-batch M over salts 1-10 (batch 0 is 3211 in every arm), and
the mean time of one cold stage (9 loops, 18 mines, two stages at a time):

| extra laws | M | cmp3d | add3 | sbo3 | per salt | stage |
|---|---|---|---|---|---|---|
| 0 | 1169 | 550 | 282 | 337 | 85-137 | 6.3 s |
| 100 | 699 | 352 | 120 | 227 | 51-90 | 7.0 s |
| 300 | 427 | 219 | 63 | 145 | 33-48 | 9.1 s |
| 1000 | 206 | 121 | 40 | 45 | 15-25 | 12.4 s |
| 3000 | 165 | 111 | 40 | 14 | 10-25 | 19.3 s |
| all | 171 | 117 | 40 | 14 | 13-22 | 21.7 s (max 30 s, 366 MB peak) |

- **M falls steeply up to about 1000 laws, then levels off.** At 1000, M is 82% lower, for twice the time. Past 3000 the
  change is noise (cmp3d 111 against 117, the only family with more than 3000 laws). The 300 row (427) is below the
  earlier control (479) because add3's phase p + 3 has only about 200 laws; here the rest come from the next phase.
- **The floor is a family's own, not the stream's.** add3 stops at 40 once all 813 of its unserved laws are in, and cmp3d
  at about 115. Mining more laws of this stream does not remove the machine proofs left on these batches. What they are:
  "What the floor is" below.
- **At large doses the loops stop being loops.** Every mine then mines the same extra laws, so the library is almost one
  library per family mined offline, and the batch it mines on matters little. That makes it closer to the own stage
  (loops warm-started from a ref mine's library) than to a cold loop. Comparing the two on the same served batches has not
  been done.

Rows: `salts_d_<n>_s<salt>.tsv`, `durations_dose.txt`. Same machine conditions.

*Renamed twins (2026-10-17).* The stream is the system's own enumeration (`pool3_sequence`: every equal pair of the
family's pool terms, shuffled), and it lists each renaming of a law's variables as a separate law. Up to renaming
variables and swapping sides, 1096 of the 1327 laws in the mined batches (batches 1 and 2 of all 9 loops) have a twin
among the extras at dose `all` (salt 1; 1064 at salt 5), and 664 at dose 1000 (salt 1). A twin needs the same rules up to
renaming (not exactly the same, since operand order follows variable names), so part of the dose effect is mining on the
test laws themselves. `MINE_TWINFREE=1` (in the same probe patch) drops
every extra whose class appears anywhere in phases 1-3. That leaves, at salt 1, 3012 extras for cmp3d, 322 for add3 and
1046 for sbo3. Mined-batch M over salts 1-10:

| extras | M | cmp3d | add3 | sbo3 |
|---|---|---|---|---|
| none | 1169 | 550 | 282 | 337 |
| 1000 with twins | 206 | 121 | 40 | 45 |
| 1000 twin-free (add3: its 322) | 388 | 169 | 123 | 96 |
| all with twins | 171 | 117 | 40 | 14 |
| all twin-free | 405 | 182 | 123 | 100 |

- **Most of the gain survives without twins.** Twin-free extras still cut M by two thirds (1169 to 388), against -82% with
  twins and -21% for the oracle ranking. At a matched count, add3's 322 twin-free extras give 123 against 63 for 300
  extras with twins.
- **Twin-free M levels off by 1000 too** (405 at `all`, within noise of 388; per salt 30-53). The floor without twins is
  about 400.
- **Renamings of laws already served give little.** `MINE_RENAME=1` (same probe patch, no extras) adds to each mine
  every renaming of x, y, z of the laws it mines on, about 490 more laws per mine and none of them unseen. Mined-batch
  M over salts 1-10 is 933 (cmp3d 466, add3 208, sbo3 259; per salt 77-120) against 1169: -20%, as much as the oracle
  ranking, without seeing the test batch, but far below twin-free new laws (388). So the twins' extra gain came from
  covering the next laws' renaming classes, not from renaming as such. For a proposer, new laws are the lever.

Rows: `salts_t_<1000|all>_s<salt>.tsv`, `salts_r_s<salt>.tsv` (renamings); `rows/floor/canon.awk` counts twins.


### No claim source with room for a model (survey, 2026-11-07)

Is there a claim source reachable from this repo where the kernel's label is expensive (seconds or more) or uncertain
(cheap checks do not decide truth or provability), so that a model ranking or budgeting claims would save work? A
read-only survey of five sources, each finding re-checked by a second reader against the cited docs (workflow
`hard-claims-survey`, no runs), found little room in all five:
- **The current loop.** Every costly tail is small, deterministic and already separated by a trivial feature: `shr1`
  presence (2652 of the 2693 screen-pass claims `verdict` leaves unproved contain `shr1`, and `prove_rule` proves all
  2693; `PARKED.md`, "Belief layer stage 2"), term size, `n` and `k`, straggler or not. The one budget a ranker could still
  spend better is the mines' (v0.6's question, "A learned scorer over the extras"), where every learned key was null.
- **`mul`.** No claim stream exists: `mul` is outside the loop's operators and is not a left-to-right machine. At a
  fixed width every variable-`mul` law is finite and decided by exhaustive evaluation, and its proof costs are smooth
  in the multiplier width and the law's arity (search-execution blend spec part 2, §58-59; "The level wall is Church's").
  The one real uncertainty, whether a width-uniform proof exists (commutativity), is a handful of theorems, not a stream.
- **Rings** (`PARKED.md`, "Port the loop to rings"; "Other theories"): a completed axiom base normalizes every law and
  a 4-point value screen decides truth; the only expensive part is an artificial node budget.
- **Vocabulary growth** (checked definitions, boolean combinations of comparisons): the one expensive and uncertain
  label is a definition's usefulness (a mine per candidate), on about 5 candidates per loop; its abbreviation form was
  decided against on a measured null (`PARKED.md`, "Definitions as an enumerator vocabulary"), and boolean combinations are capped
  at about 17% of head-start M (`PARKED.md`, "Boolean combinations of comparisons").
- **External corpora.** Souper's `test/Infer` gives 14 cases in the term language, at most two variables, which cost
  milliseconds by the loop's per-law costs (inference, not run); its other 25 files have no encoding here, and the
  InstCombine corpus is unread (`PARKED.md`, "LLVM InstCombine tests as a corpus").

Reading: in this kernel's reach, a claim's label is either cheap and decided or out of reach, and what separates the
two is syntax, so goal 3's model has nothing to learn that a lookup does not already know (inference across the five
sources; no model was tried). The cheapest falsifiers named: prove the 14 Souper cases and log each route (minutes); time
a generated pool of variable-`mul` laws by the case-split prover at widths 2-3 and look for spread within an
(n, arity) cell that size does not predict (minutes to tens of minutes).
