### Selecting the extras by straggler verdict: better per n, not per CPU (2026-10-31; v0.6, second try)

Question (`docs/superpowers/specs/2026-10-31-context-aware-selector-design.md`): does filling each mine's n extra slots with
laws the mine's own base rules mark as stragglers (the first n of a 4n pool, `EXTRAS_SELECT=straggler`, selection inside
`rule_miner` via `RULEMINER_EXTRAS_*`) move the frontier past a random draw at the same mining CPU? Only stragglers can earn
a rule; 37% of random extras are stragglers (`2026-10-31-v06-labels`). The pool always held at least n stragglers (18 of 18
mines logged, kept-straggler share 1.000), so every extra slot was a straggler. Classifying the pool costs 0.1-0.2 s per mine.
Gates `v06h-g1` to `g5`, salts 1-3 (disjoint from any training), Defender real-time protection off, machine 36-50% loaded by
other apps, untimed counts. Summed over the salts:

| arm | held-out M | job CPU | CPU vs random, same n |
|---|---|---|---|
| random n 80 / straggler n 80 | 6043 / 5347 | 359 / 492 s | 1.37x |
| random n 160 / straggler n 160 | 5517 / 4931 | 446 / 841 s | 1.89x |
| random n 319 / straggler n 319 | 5166 / 4498 | 674 / 1252 s | 1.86x |
| random n 638 (g5) | 4600 | 910 s | |
| pool 4, first n (control, g4) | 5168 | 628 s | |

Sigma = 76 (redraw spread, `2026-10-31-v06-g*`). The control is within it (5168 against 5166), so the pool alone moves
nothing. The straggler arm is better than random at every n by 586-696 held-out M, beyond sigma, but costs 1.4-1.9x the job
CPU (more rules to prove: walk/match/op counts 1.3x the random n 638 arm).

- **Verdict by the pre-registered rule: null.** Rule (a) (held(h_n) < held(r_n) - sigma at CPU <= 1.1x) fails at every n on
  CPU. Rule (b) (held(h_n) <= held(r_2n) at lower CPU): 4498 <= 4600 holds, but 1252 s against 910 s is higher, so it fails.
  The earlier recorded n 688 point (4622 at 1247 s) agrees on the held-out side and not on cost; the r638 arm here ran at
  910 s on a lighter machine, so the CPU gap is real but its size carries load noise.
- **Reading (inference).** The straggler verdict does choose better extras per slot, and the gain is bigger than a doubling
  of n would give per law, but doubling n is the cheaper way to buy held-out M: random 319 to 638 gains 566 M for 236 s, the
  straggler choice at 319 gains 668 M for 578 s over random 319, and over random 638 only 102 M for 342 s. What would
  confirm: a cheaper straggler arm (pool 2, or n 100) read against the random curve between n 160 and 319, where the
  straggler arm's CPU would meet random's. Not run.
- **Null scope.** "Straggler-first selection does not beat doubling n at equal CPU", not "the base rules' verdict carries
  no signal". Marginal selection (h1b: prefer stragglers whose candidate left side no kept law has yet) is not run; it
  would target the same cost (`PARKED.md`, "Learned proposer").
- Runs: `2026-10-31-v06h-smoke`, `v06h-g1` to `g5`.

#### The cheap variant: a better point on the curve (2026-10-31; runs `v06c-g1` to `g5`)

`EXTRAS_SELECT=cheap` keeps, of the pool's stragglers, the n with the fewest rewrite steps spent classifying them (spec
addendum, rule set before data). Salts 1-3, pool 4, Defender real-time protection off, machine 74-75% loaded by other apps:

| arm | held-out M | job CPU | walk work |
|---|---|---|---|
| cheap n 160 | 4721 | 700 s | 488 M |
| cheap n 319 | 4666 | 1158 s | 965 M |
| random n 160 / 319 / 345 / 433 / 638 | 5517 / 5166 / 5023 / 4832 / 4600 | 446 / 674 / 608 / 669 / 910 s | 157 / 362 / 388 / 485 / - M |
| straggler-first n 160 / 319 | 4931 / 4498 | 841 / 1252 s | |

- **Pre-registered rule: null, narrowly.** (a) fails on CPU (700 s against 446 s). (b) c160 holds the held-out side against r319 (4721 <= 5166), but
  700 s is above r319's 674 s by 26 s; c319 (4666) misses r638 (4600). Cheap n 160 sits left of straggler-first n 160
  (4721 at 700 s against 4931 at 841 s): the cost key keeps the gain and drops part of the cost.
- **Post-hoc control at matched work** (set before its data, in the spec addendum): random n 433 has the same walk work as
  c160 (485 M against 488 M). Salts 1-3 (`v06c-g4`): 4721 against 4832, **-111** (sigma 76), job CPU 700 against 669 s
  (1.05x). Fresh salts 4-6 (`v06c-g5`): 4569 against 4774, **-205**, 887 against 860 s (1.03x). Both pass. The random arms'
  job CPU swings with load (r319 674 s, r345 608 s), so the CPU ratios carry about +-10%; the work counts do not.
- **Reading (inference).** Among the pool's stragglers the cheap ones carry more held-out gain per unit of mine work than a
  random draw gives, up to n about 160; at n 319 the cheap pool is spent and the arm costs what straggler-first costs.
  What would confirm: cheap at n 80 and 240 (the knee), and a replication of g4 at the other pool sizes. The milestone
  rule was not met, so this is a better point, not the rule's win. Gain 111-205 held-out M of about 4800 (2-4%).


- **Knee chart (2026-10-31; runs `v06k-g1` to `g12`; rule in the spec addendum, set before the data).** Each cheap arm against the
  random arm of equal walk work (the random n from the walk-per-n of the recorded arms), salts 1-3 | 4-6, held-out M (job CPU):

| cheap arm (pool 4 unless noted) | salts | cheap (job CPU) | random of equal work (job CPU) | difference | wins |
|---|---|---|---|---|---|
| n 80 (walk 219 M, 224 M) | 1-3 | 5427 (444 s) | 5531, n 208 (684 s) | -104 | yes |
| n 80 | 4-6 | 5305 (656 s) | 5476 (688 s) | -171 | yes |
| n 160 (walk 488 M, 545 M) | 1-3 | 4721 (700 s) | 4832, n 433 (669 s) | -111 | yes |
| n 160 | 4-6 | 4569 (887 s) | 4774 (860 s) | -205 | yes |
| n 240 (walk 780 M, 784 M) | 1-3 | 4543 (1260 s) | 4377, n 700 (1422 s) | **+166** | no |
| n 240 | 4-6 | 4591 (1359 s) | 4434 (1207 s) | **+157** | no |
| n 160, pool 8 (walk 555 M, 525 M) | 1-3 | 4990 (920 s) | 4860, n 495 (985 s) | **+130** | no |
| n 160, pool 8 | 4-6 | 4718 (967 s) | 4717 (1081 s) | +1 | no |

  Sigma 76. So cheap selection beats a random draw of equal work at n 80 and n 160 (by 104-205 held-out M, 2-3% of the
  total, on both salt sets) and loses at n 240 (+157-166) and with a pool of 8 (no gain, and more work than pool 4 at n 160:
  4990 against 4721 on salts 1-3). The advantage lasts up to about 500 M of walk work (700-900 s of job CPU) and reverses past
  it.
- **Reading (inference).** The cheapest stragglers of a pool are worth more than a random law per unit of work, and the
  pool of 4n holds only so many of them: past n about 160 the kept laws are the dearer stragglers and the arm pays what
  straggler-first pays. What would confirm: the kept laws' steps per n (not logged). A larger pool did not help, which fits (the pool is not the limit; the cost key is).

- **Coverage keys (2026-10-31; runs `v06n-g1` to `g4`; rule in the spec addendum "c1: coverage keys").** `novel` and `reinforce`
  rank the pool's stragglers by whether a candidate left side the served stragglers propose reaches them, then by steps. At
  n 160, pool 4, against `cheap` rerun on the new exe (identity: 4721 and 4569 held-out M reproduced, walk counts equal to the
  recorded arm):

| key | salts | held-out M | against cheap | job CPU against cheap | wins |
|---|---|---|---|---|---|
| novel | 1-3 | 4721 | 0 | 1628 s against 1593 s | no |
| novel | 4-6 | 4569 | 0 | 1573 s against 1528 s | no |
| reinforce | 1-3 | 4723 | +2 | 1549 s against 1593 s | no |
| reinforce | 4-6 | 4612 | +43 | 1359 s against 1528 s | no |

  Null on both keys (sigma 76). The cause is visible in the logs: the class is nearly constant. Of the kept stragglers, 99-100%
  are reached (`RULEMINER extras reached`: mine 0 kept 160 of 160 with the pool 302 of 302; mine 1 142 of 143), because the
  candidates are abstract patterns that match some subterm of almost any straggler's normal form. So both keys reduce to
  `cheap` and the direction question is untested, not answered. `novel` reproduced `cheap`'s rules in 9 of 9 loops on salts 4-6.
  What a sharper test needs: a class that splits the pool (for example reached by a candidate that the served stragglers'
  greedy pass would choose, or the number of distinct candidates reaching), which is a new design, not a rerun.

- **Crossover and steps (2026-10-31; runs `v06h2-g1` to `g6`; same rule as the knee chart).** `cheap` at n 120, 200 and 240
  against a random arm of near-equal walk work (n 310, 570, 700), salts 1-3 | 4-6, held-out M (job CPU), sigma 76:

| cheap arm (pool 4) | salts | cheap | random | difference | wins |
|---|---|---|---|---|---|
| n 120 (walk 334 M, 338 M) | 1-3 | 5057 (1088 s) | 5251, n 310, walk 353 M (1196 s) | -194 | yes |
| n 120 | 4-6 | 5032 (1053 s) | 5110, walk 386 M (1221 s) | -78 | yes (2 past sigma; the random arm did 14% more work) |
| n 200 (walk 646 M, 664 M) | 1-3 | 4700 (1554 s) | 4537, n 570, walk 671 M (1742 s) | **+163** | no |
| n 200 | 4-6 | 4742 (1474 s) | 4606, walk 679 M (1822 s) | **+136** | no |
| n 240 (walk 780 M, 784 M) | 1-3 | 4543 (1550 s) | 4377, n 700 (1422 s) | +166 | no (reproduces `v06k-g5`) |
| n 240 | 4-6 | 4591 (1419 s) | 4434 (1207 s) | +157 | no |

  With the knee chart: wins at n 80, 120 and 160, loses at n 200 and 240; the crossover lies between n 160 and n 200 (about
  500-650 M of walk work). The new `RULEMINER extras steps` lines show why the ranking is thin:
  - **Mine 0 has no key.** The kept stragglers' steps sum to 0 in every mine 0 (empty base): steps count applications of mined
    rules, and there are none, so `cheap` is straggler-first in stream order there, about half the extras.
  - **Mine 1 runs out of choice.** Its pool holds 114-249 stragglers (n 120 to 240) against n of 120-240, so past n about 160
    it keeps nearly all of them (n 240: 221 of 221, 232 of 232) and fills the rest with clean laws; the key has nothing left to
    rank. Earlier "the dearer stragglers" is not what the logs show; the pool simply has no cheap tail to choose from.
  - So `cheap` helps when it can leave stragglers out of the mine 1 pool (n at most about 160 of about 150-200 stragglers)
    and costs what straggler-first costs when it cannot. A larger pool did not help (pool 8, n 160) because the pool's extra
    stragglers raise the work for a key that only ranks by mined-rule steps.

- **Graded reach keys (2026-10-31; runs `v06g2-probe`, `v06g2-g1` to `g4`; rule in the spec addendum "g2").** The class is the
  number of candidate left sides (from the served stragglers) that reach a straggler: 11-18 distinct values per pool, correlation
  with steps about 0 (-0.02 to 0.11), so unlike the binary class it splits the pool. `novel` keeps the fewest-reached first,
  `reinforce` the most, each then by steps. At n 160, pool 4, against `cheap` (4721 and 4569):

| key | salts | held-out M | against cheap | walk against cheap | wins |
|---|---|---|---|---|---|
| novel | 1-3 | 4807 | +86 | 472 M against 488 M | no |
| novel | 4-6 | 4657 | +88 | 499 M against 545 M | no |
| reinforce | 1-3 | 5035 | +314 | 483 M against 488 M | no |
| reinforce | 4-6 | 4545 | -24 | 500 M against 545 M | no |

  Null on both (sigma 76). `novel` is worse on both salt sets by 86-88 (it also did 3-9% less work, which explains part of
  that); `reinforce` swings from +314 to -24, so it is noise around `cheap` or worse. The rules changed in every loop (0 of 9
  same), so the key does move the mine; it just does not move it toward a better frontier. Reach by served candidates is not a
  useful signal for choosing extras, in either direction. With the binary class (`v06n-g1` to `g4`) and the stage-1 scorer this
  is the third per-law signal that fails to beat `cheap`/random.

- **A key under an empty base (2026-10-31; runs `v06j3-g1`, `g2`; rule in the spec addendum "j3").** `small` ranks by (steps,
  normal-form size): `cheap` with ties by size in mine 1, smallest normal form first in mine 0. n 160, pool 4, against `cheap`
  (the recorded arm, 4721 and 4569):

| salts | held-out M | against cheap | walk | match | op | job CPU |
|---|---|---|---|---|---|---|
| 1-3 | 4690 | -31 | 490 M against 488 M | 3.12 G against 3.24 G (-3.7%) | 1.60 G against 1.70 G (-5.7%) | 1073 s against 1240 s |
| 4-6 | 4591 | +22 | 533 M against 545 M | 3.11 G against 3.45 G (-9.7%) | 1.58 G against 1.85 G (-14.7%) | 1078 s against 1279 s |

  Not a win by the rule (neither difference passes sigma 76). Held-out M is the same within noise; work counts are lower on
  match and op (4-15%) at equal walk, which points at real saving, and job CPU is 13-16% lower, which meets the cost-win line
  (<= 0.9x on both sets). Caveat: the `cheap` job CPU is a cached earlier measurement (1240 s and 1279 s) and the same arm read
  1593 s and 1528 s under load in `v06n-g1` and `g3`, so the CPU ratio is not reliable; the deterministic counts are. The rules
  differ in every loop (0 of 9 same). The instruction count settles it:
  Instruction counts (`icount.ps1` method, `-Mode pmc` on CPU 4, whole `driver::sweep` salt 1 at n 160, summed over the three
  loop processes; runs `v06j3-icount` for `cheap`, `v06j3-icount-sm` for `small`, 2 runs each; the first `small` trace lost
  events and was discarded, the machine at 44% load): `cheap` 2351.25 G and 2351.79 G; `small` 2306.71 G and 2304.61 G. So
  `small` does 1.95% fewer instructions, against a spread of 0.02% (`cheap`) and 0.09% (`small`): real and well above noise,
  and an order of magnitude below the 13-16% the job CPU suggested (load noise). Per loop the cost moves both ways (loop 2
  388 G to 449 G, loop 3 883 G to 776 G), as the rules differ. One salt only; a cost claim of about 2%.
  `EXTRAS_SELECT` is now `first` or `small`; the earlier keys named in the sections above ran as recorded and are deleted from the code (recover from `6bdf573`).

