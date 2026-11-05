## The frontier and v0.5

### The frontier: the probe and the gate (2026-10-24/25)

*The frontier past the loops' sizes (2026-10-24; run `2026-10-24-frontier-probe`, 7.7 min; throwaway probe
`classes::probe_frontier`, `docs/runs/2026-10-24/patches/frontier_probe.patch` on 8d190d9, reverted; scripts
`docs/runs/2026-10-24/scripts/frontier_probe.sh`, `frontier_watch.sh`).* Class-table spec §7 (phase 3) asks for the
frontier by law size; the loops serve laws up to size 13 (two growths of representatives up to size 9, two nodes per
growth), and ROADMAP v0.5 wants held-out laws larger than they serve. The probe grows the 56 streams at `HELD_SALT`
three and four times (`stream_laws`, budget 20000 per level, interleaved as `stream_sequence`), takes each odd band's
first 1000 laws, and runs the held-out check (`CHECK_FAST`) on each under salt 6's three loop rule sets (run
`cache-check-1`) and under no mined rules (the table alone). Free share = laws proved with no whole-term machine proof,
of 1000; best loop / worst loop / none:

| growths | band 11 | band 13 | band 15 | band 17 |
|---|---|---|---|---|
| 3 | .93 / .91 / .79 | .79 / .76 / .69 | .76 / .72 / .63 | |
| 4 | .93 / .91 / .79 | .79 / .76 / .68 | .75 / .72 / .62 | .69 / .66 / .60 |

- **Cheap, once.** Three growths: 132428 laws in 137 s; four: 229415 laws in 212 s (band 15 77296, band 17 84279),
  peak commit about 3.3 GB. Held-out files are written once (`regenerate_held`), so a sweep pays none of it; each extra
  band costs the gate about 1.3 s per loop. (The probe script's own watchdog matched nothing, since the output path
  reached the exe through the environment, so only the four-growth run's peak was measured.)
- **The 50% line is past size 17.** The free share falls 14 points from band 11 to 13, then 4-6 points per band: about
  .69 at 17 with the loops' rules and .60 without. A threshold at 50% would read "beyond the largest band" for every
  arm, so it cannot be the headline; the per-band shares are.
- **Mined rules carry to sizes the loops never served.** Over the table alone, the loops' rules free 12-14 points at
  band 11, 8-11 at 13, 9-13 at 15 and 6-9 at 17: mining's gain shrinks slowly with size and stays well above the
  spread between loops (2-4 points).
- **Bands 11-15 do not depend on the growth count.** Three and four growths give the same shares within 1 point, so
  the extra growth only adds band 17.
- About 3-13% of each band is not proved at all under `CHECK_FAST` (27-130 laws, most with no rules); M counts them
  with the machine proofs, as the gate does.

*The frontier on the gate (2026-10-25; plan docs/superpowers/plans/2026-10-24-class-table-phase-3.md; runs
`2026-10-24-held-15-17-2`, `2026-10-24-phase3-baseline`).* The held-out set has four bands now: `held_15.txt` and
`held_17.txt` beside 11 and 13, each band drawn from the fewest growths that reach it (`held_levels`: 2, 2, 3, 4), so
11 and 13 are unchanged and 15 and 17 are byte for byte the probe's above. Every arm checks each band under its three
loops' rules and under the table alone (no mined rules), and the gate prints one `bands` line per arm. The baseline,
an A/A of 489cdd7 on salts 1-10 (untimed, 2 arms at a time, 57 min), pooled over salts and loops (free share; M per
1000 laws checked: the check keeps the laws plausible at widths 1-6, 1000, 999, 997 and 994 per band, so 30 loops'
M per band is the column times 30 times that count over 1000, 2307, 6414, 7569 and 9385):

| band | loops' free share | table's | gain (points) | loops' M | table's M |
|---|---|---|---|---|---|
| 11 | .923 | .762 | 16.1 | 76.9 | 238.0 |
| 13 | .786 | .693 | 9.3 | 214.0 | 307.3 |
| 15 | .747 | .635 | 11.2 | 253.1 | 365.1 |
| 17 | .685 | .602 | 8.3 | 314.7 | 398.4 |

- **Repeats.** A and B agree on every number; M 1718, rules the same in 30 of 30 loops. The table's lines are
  identical in all 20 arms (it does not depend on the salt), and salt 6's lines for 15 and 17 equal the probe's
  (same rules). The loops mined 45-73 rules each (mean 57.9).
- **The held total changed scope.** `held` in the salt and total lines is now the loops' M over all four bands
  (25675 here); the old two-band total is bands 11 and 13 of the per-band sums, 2307 + 6414 = 8721, the 2026-10-23
  baseline's exactly. The ablations driver's "held-out rise" now guards bands 15 and 17 too.
- **What a change must move.** Mining's gain falls from 16 points at band 11 to 8 at band 17 but stays well above the
  spread between loops (salt 6: 3-4 points at 15 and 17), so the gain at the largest bands is the frontier's measure;
  no band nears 50% (decision D2 of the plan: no threshold).
- **The baseline since 2026-10-26** is ab6f4a7 (the three-variable pool, no lookahead, and the every-input fallback;
  "Kept: the every-input fallback" below), arm B of `2026-10-26-everyinput-ab`: M 1562, held-out M 21905, and per band
  (the table's columns unchanged):

  | band | loops' free share | gain (points) | loops' M |
  |---|---|---|---|
  | 11 | .942 | 18.0 | 57.7 |
  | 13 | .820 | 12.7 | 180.3 |
  | 15 | .787 | 15.2 | 213.2 |
  | 17 | .718 | 11.6 | 281.5 |

  New levers gate against its exe, `2026-10-26-everyinput-exes\E.exe` (the numbers above, which 23b89fa repeats, are
  `2026-10-26-pool3-exes\H.exe`'s; 411aacf's are `2026-10-26-keep-exes\K.exe`). The three exes' arms for salts 1-10
  are in the untimed gates' `ARM_CACHE`, so arm A reruns nothing until `streams_ab.sh` or `runs.exe` changes (they are
  part of the cache key).

### Definitions and transfer for v0.4 (2026-10-25)

*Where a loop's definitions should come from (2026-10-25; v0.4 design; run `2026-10-25-held-unsettled`, about 1 min,
throwaway scripts `defprobe.py` and `held_unsettled.sh` with their output in the run folder).* v0.4 was to build
definitions as a vocabulary of the enumerators, mined per loop (decided 2026-10-25; since the rescope that day one of v0.4's levers, `ROADMAP.md`; decided against 2026-10-26, "They do not transfer" below; the alternatives are parked in
`PARKED.md`, "A library of mined definitions that outlives the loop" and "Defined operators inside `Term`"). The probe
asks which laws a loop should compress into definitions: (1) the served laws its rules left to a whole-term machine
proof, or (2) every law it served. A definition is a fragment of 2-4 operators cut from a subterm, its holes the cut
subterms and variables (one hole per distinct subterm); one use saves its operators less one; each loop keeps its top
5 by total saving. Corpora: the 30 loops of arm A of `2026-10-24-phase3-baseline` (300 laws served per loop, 39.1 left
to a machine proof on average; laws not proved at all print no line and are left out). The held-out laws each loop
leaves to a machine proof were recovered by rerunning the gate's held-out check on salts 1-3 (9 loops) with its
`MACHINE` lines kept; its counts equal the baseline's.
- **Source (1) is not noise.** 4.97 of its 5 definitions per loop occur in at least 3 of the loop's ~39 laws.
- **Source (2) finds what the rules already settle.** Its lists are nearly the same in every loop: association chains
  (`add(□, add(□, □))` and `add(add(□, □), □)` in 30 of 30 loops, `xor(□, xor(□, □))` 30, `xor(xor(□, □), □)` 21), shapes
  the fixed `assoc` rules normalize, plus `sub(□, sub(□, □))` (28). Source (1)'s lists vary by loop and are mostly
  `sub` under other operators (`sub(□, sub(□, □))` 29 loops, `and(□, sub(□, □))` 22, `sub(sub(□, □), □)` 12,
  `shl1(sub(□, □), □)` 9). The two lists share 1.4 of 5.
- **Source (1)'s definitions carry to larger held-out laws, and to the unsettled ones more than the rest.** Share of
  held-out laws holding one of the loop's definitions, on those left to a machine proof against all of the band
  (salts 1-3): (1) .45/.37 at 11, .56/.35 at 13, .52/.37 at 15, .53/.38 at 17; (2) .63/.69, .62/.64, .64/.68,
  .71/.69. Saving per unsettled held-out law: (1) 1.06, 1.82, 1.74, 1.98; (2) 1.11, 1.59, 1.76, 2.33. So (2) touches
  more held-out laws and saves as much on the unsettled ones, but evenly on settled and unsettled laws, with shapes
  the rules already handle; (1) is enriched 1.2-1.6 times in the unsettled laws.
- **What the probe cannot see.** Saving is a proxy: a definition pays only if the miner finds a rule over it that
  settles laws, and an association chain's rules exist already. All but 28 of the 300 top definitions have 2 operators (27 of the 28 in source
  (1)). `shl1`'s unused second argument shows as a hole (`shl1(sub(□, □), □)`); a definition of it would take one
  argument fewer.
- **The miner's pool is not where reach is short (run `2026-10-25-pool-bottleneck`, about 9 min; patch, script and
  totals in its folder).** Each loop's 300 served laws under its final rules leave 741 stragglers over the 30 loops
  (24.7 a loop; fewer than the 39.1 served with a machine proof, since later batches' rules settle earlier laws).
  Mined again on those stragglers (as the loop mines: `RULEMINER_FAST=1`), a pool of right sides up to 7 nodes instead
  of 5 (415,788 terms instead of 5,804, more than a vocabulary of 2-operator definitions at size 5 would add) covers
  358 instead of 355. Every straggler already has a candidate from the size-5 pool; the 9-node pattern cap cuts 300
  patterns, 171 of which have a right side. 302 of the 355 laws covered are covered by rules over 3 or 4 variables:
  the cross-side route (subterms and patterns up to 13 nodes, `RULEMINER_VARS` 4), not the pool. So a vocabulary in
  the pool would buy about 1%; if definitions buy reach, it is in the cross-side route's caps, or in what the 386
  uncovered stragglers lack.
- **Nor are the cross-side caps (run `2026-10-25-cross-caps`, about 12 min).** The same stragglers mined with the
  cross-side route's caps at 17 nodes and 4 variables cover 373 of 741 (355 now); at 25 and 6, about no cap, 375. The
  candidate cap (400) is never reached (at most 133 a loop). So no reach a vocabulary could give the miner covers more
  than 20 of the 741 (2.7%); 366 stay uncovered with every size cap lifted. Reach through definitions has no lever
  in the miner as it stands; the deficit is in what the 366 lack.
- **What the uncovered stragglers lack: a prover for `shr1` (run `2026-10-25-uncovered`, about 3 min; classifier patch,
  `classify.py` and `classes.txt` in its folder).** Of the 386 stragglers left uncovered under the current caps, 355
  are laws the rewriter never closes (`UNPROVED`), and all 355 have `shr1` (322 with both arithmetic and bitwise
  operators, 33 arithmetic only). `Machine::parse` refuses `shr1`, so nothing proves them; that is 48% of all 741
  stragglers. The other 31 are machine-proved laws, 28 of them with no equal pair of subterms across the sides short
  of the whole sides (only a whole-law rule covers them). All but one uncovered straggler has candidates; 149 have a
  proper equal pair. Median 10 operators a law. The parked prover is `PARKED.md`, "A prover that knows what `shr1`
  means".
- **A third of the gate's M is `shr1` laws nothing proves (run `2026-10-25-m-shr1`, about 4 min).** The serve check
  replayed on each of the 90 batches of arm A under the rules that batch had (every batch's M equal to its `m.tsv`
  row), patched to name the laws it does not prove: M 1718, of which 545 are unproved and all 545 have `shr1`; only 4
  of the 1173 machine-proved laws have it. The share is the same in every batch (32%, 33%, 31% for batches 0-2):
  mined rules cut the `shr1` laws (253, 151, 141) as fast as the rest (549, 305, 315), not faster. Nothing in vocabulary or the
  miner's caps reaches them; and since M counts machine proofs too, a prover lowers M only through the rules it lets
  the miner keep (next bullet).
- **Even free `shr1` rules cut M by only 6% (run `2026-10-25-shr1-oracle`, A/B gate, salts 1-10, 76 min untimed).**
  Arm B is HEAD (6d3d20c) with an oracle in the miner's rule proof (`Prover::holds`): an arithmetic rule with `shr1`
  that nothing proves is kept when it holds exhaustively at widths 1-4 over at most 5 variables (`probe.patch` in
  `2026-10-25-shr1-oracle-exes`). Arm A (unpatched, same commit) gave the baseline's numbers salt for salt. B kept 120
  `shr1` rules in its final loops against A's 31 (661 rules against 577), and M fell 1718 to 1620 (-5.7%, every salt
  4-14 lower): the unproved laws 545 to 445, the machine proofs 1173 to 1175. Held-out M 25675 to 23581 (-8.2%); free
  share 11 .923 to .938, 13 .786 to .810, 15 .747 to .765, 17 .685 to .698; job CPU 7481 to 3963 s. So 445 of the 545
  `shr1` laws stay unproved with rules that cost nothing to prove, and a `shr1` prover that only admits rules is worth
  at most about 100 of M at this miner (why: next bullet).
- **Most of the rest is laws seen first, not laws the miner misses (run `2026-10-25-why-uncovered`, about 3 min).**
  Batch 0 is served with no rules, so its M (803 of 1718, both arms) is out of any rule's reach; the oracle's cut is all
  in batches 1-2, 915 to 817 (-10.7%), its `shr1` share 292 to 192 (batch 0's 253 assumed unchanged, as its M is). And a
  served law the loop's rules miss is one the miner closes once it has seen it: arm B's 30 loops mined again on their
  own 300 served laws under their final rules, with the oracle (`BNECK3` in the run's `probe.patch`), leave 489
  stragglers and cover 416. Of the 73 uncovered (41 unproved with `shr1`, 31 machine-proved without, 1 machine-proved
  with), every one has candidates matching its normal forms that prove, and no candidate closes it alone. So what M
  measures in batches 1-2 is how far rules mined from earlier batches carry to laws not yet seen, not the miner's reach
  on what it has seen.
- **`shr1` rules carry to unseen laws as well as the rest, and better with the oracle (run `2026-10-25-held-shr1-2`,
  12 min).** The held-out check of every band under no rules and under each loop's final rules, arms A and B, naming the
  unproved laws (`probe.patch` in the run folder). With no rules nearly every held-out `shr1` law is unproved (81-123 a
  band, 1-5 machine-proved) and no other law is (155-280 machine-proved). Share of those laws the final rules make free,
  `shr1` against the rest, by band 11/13/15/17: arm A .65/.33/.41/.36 against .70/.31/.28/.19; arm B .84/.56/.56/.48
  against .70/.31/.28/.19. Held-out M per loop, A to B: `shr1` 251.5 to 179.1 (-29%), the rest 604.4 to 607.1 (the
  totals 855.9 and 786.2 match the gate's). So a `shr1` prover's rules would carry; but most held-out M is laws without
  `shr1` that the rules leave to a machine proof (604 of 856), and those carry worst as laws grow (.19 at band 17). The
  check's `CLASS_UNUSABLE` lines (e.g. `shr1(add(x, x), 0) = and(x, shr1(-1, 0))`) are class-table replacements
  `verdict` cannot prove, as it takes a `shr1` subterm for an atom, not mined rules refused: those nodes fall back to
  the rules (`PARKED.md`, "Verdicts for replacements with a shift subterm").
- **Laws without `shr1` take about a rule each, and at band 17 half stay out of reach even when seen (run
  `2026-10-25-held-seen`, 111 min).** For each arm-A loop, the held-out laws without `shr1` its final rules leave to a
  machine proof (run `2026-10-25-held-shr1-2`), mined under those rules as the loop mines (HEAD build): band 11, 1434 of
  1437 covered with 1127 rules (0.79 a law); band 17 (29 of 30 loops: the 30th's mine reached a join step 69 levels deep, past
  `StepPath`'s 64 bits, and hung after the worker panicked; fixed in 15d7223 and c29cff1, it then covers 91 of 199
  with 77 rules, run `2026-10-25-join-depth-repro`),
  3451 of 6892 covered (50%) with 2696 rules (0.78 a covered law), and the 400-candidate cap hit in 12 of the 29 mines
  (band 11: 139 candidates a mine). The rules are small (mean left side 4.5 and 4.3 operators) and 86% and 69% have 3+
  variables; the same rules recur across loops, as the loops see the same held-out laws (157 and 472 distinct). So a
  rule mined on one law rarely closes another: what carries poorly to unseen laws is rules in general, not `shr1`
  rules, and at band 17 the miner's candidates also run out.
- **Lifting the rules to their most general provable form carries nothing further (run `2026-10-25-rule-lift`, 6 min
  untimed; v0.4's first lever).** Every distinct rule of arm A's 30 final rule sets (1287) made as general as still
  proves, greedily: a left-side constant to a fresh variable (alone or with the same constant on the right), or one
  occurrence of a repeated left-side variable to a fresh one, each step screened (`is_law`) and proved by the miner's
  `Prover` (built-in rules only, width 4; `lift.patch`, `miner::lift_probe`). 460 lift (433 constant steps, 174 of them
  on both sides, and 1 split), 284 of them only by freeing `shl1`'s unused second argument. Each loop's rules with its
  rules lifted, through the gate's held-out check, against the originals' (run `2026-10-25-held-shr1-2`; an A/A on s1
  l1 b17 matched): free share 11 .923 to .922, 13 .786 to .786, 15 .747 to .748, 17 .685 to .686; held-out M 25675 to
  25652 (-0.1%), loops better and worse about evenly at 11 and 13 and 2 to 1 at 15 and 17; exhausted laws at 17 71 to
  35. Most constants cannot be freed (827 rules lift not at all, and 284 of the 460 only free `shl1`'s unused
  argument), and where one can, reach does not move: what a rule lacks to carry is its shape, not its generality.
- **Rules mined on laws close them but few others: their left sides are law-sized (run `2026-10-25-rule-transfer`, 10
  min untimed).** Each arm-A loop's final rules plus the rules its held-seen mines chose (3900 over 60 mines), through
  the held-out check of every band, against the loop's rules alone (`xfer.sh`, `xfer.py` in the run folder). Of the
  laws the loop's rules leave unfree (machine-proved or unproved), the seen rules make free: mined on band 11, .624 of
  band 11 (seen) but .044, .048 and .034 of bands 13, 15 and 17; mined on 17, .330 of band 17 (seen), .131 of 15, .084
  of 13, and at band 11 they lose 144 laws (-.062): rules made for large laws break small ones. Within a mine,
  half or more of the laws closed (.61 on 11, .50 on 17) are closed by rules that close exactly one, and closure falls
  with the left side's size: on band 17, left sides of 1 and 2 operators close 3.32 and 2.19 laws each, 5 and 6 close
  1.00 and 0.88; 1584 of the 2773 band-17 rules have left sides of 5 or 6 operators. A left side that size matches
  few laws: in each band's held-out laws as written (not normal forms), 88-97% of the rules that closed one law match a
  subterm of under 1% of the laws, as do 94-96% of a sample of 300 of the loops' own rules; rules that closed two or more
  are smaller (3.4-3.5 operators against 4.6-4.7) and match more (mean 1.1-2.7% against 0.4-0.9%). So a mined rule is
  mostly a fragment of the law it was mined on, and carries as far as that fragment recurs.
- **Capping the rules small carries less in all, though more per rule (run `2026-10-25-xsize-ab`, 48 min untimed).**
  The gate A/B with the miner's cross-side route capped (subterms and pattern of size at most 9, arm A, or 7, arm B,
  against the hardcoded 13; `xsize7.patch` in `2026-10-25-xsize-exes`), against arm A of `2026-10-25-shr1-oracle`.
  The two caps agree (rules the same in 29 of 30 loops): below 13 the cross-side route adds next to nothing beyond
  the pool route. The loops keep 467 final rules against 1738; M 1718 to 2207 (+28%), held-out M 25675 to 33740
  (+31%), free share 11 .923 to .822, 13 .786 to .725, 15 .747 to .687, 17 .685 to .637 (table alone .762, .693,
  .635, .602); job CPU 7481 to 4090 s an arm. Per rule the small ones do carry further: above the table they free
  12.8e-5 of band 11 and 7.5e-5 of band 17 each, and the 1271 rules the cap removes 7.9e-5 and 3.8e-5. But the large
  rules still free about 60% of what the rules free on every band, held-out included, so a size cap is no lever:
  what would carry is small rules the miner does not yet find, not fewer large ones.

### The pool over three variables and every-input proofs (2026-10-26)
- **A pool route over three variables finds them: held-out M -6.9% (run `2026-10-26-pool3-ab`, 62 min untimed).**
  Small rules came only from the pool route (patterns over at most two variables, a smaller equal term from the pool
  of terms up to 5 nodes), and every rule over three or more from the cross-side route, tied to one law's two sides.
  Arm B lets the pool route abstract into three variables, with `v2` in the pool (10280 terms, 1361 distinct
  functions, against 5804 and 617); `lt` patterns stay over two, on an estimate of 3.7 GB for the `lt` index over
  three that was wrong (about 105 MB; see "Kept" below) (`pool3.patch` in `2026-10-26-pool3-exes`); the cross-side route unchanged, so the arm only adds candidates
  (about 10% more a mine). Arm A, HEAD, repeats the baseline exactly (M 1718, held 25675). B: M 1718 to 1672 (-2.7%),
  held-out M 25675 to 23897 (-6.9%, lower on every salt), free share 11 .923 to .926, 13 .786 to .797, 15 .747 to
  .768, 17 .685 to .709: the gain grows with the band, the first lever whose reach does. Rules 1738 to 1665; left
  sides of 1 to 3 operators over three or more variables 146 to 267, of 5 or 6 operators 1070 to 922 (mean 4.31 to
  4.09 operators). The cost: job CPU 5451 to 10019 s (1.84x). Against the `shr1` oracle's ceiling (held-out M -8.2%,
  run `2026-10-25-shr1-oracle`) this is most of that size at no new prover. Throwaway: keeping it is its own change.
  Where the CPU goes (the mines' `RULEMINER time` lines, summed over the 60 mines of each arm): candidate generation
  stays at about 1 s; the scoring rounds take 1554 to 3136 s and the rule-set evaluations 737 to 1080 s. Rounds 7602 to
  11211, with the main path's (a winner or a rollback each) 2183 to 1981, so the lookahead's greedy paths
  ("Preferences and rival orientations in the miner") take about 5400 to 9200: a round's winner now has a rival (another
  right side of its own left side) that gains more in 63 rounds against 21, and the lookahead keeps the rival in 11
  against 2. Each round also scans more candidates (163 to 205; the gain bound skips 39% of scorings against 43%). So the
  cost is rival swaps, each checked by two whole greedy paths; more winners come with a rival likely because a small
  pattern over three variables has several equal small terms in the pool (not measured).
- **With small rules, the lookahead buys nothing: take the rival (run `2026-10-26-lookoff-ab`, 48 min untimed).** The
  3-variable pool with the lookahead off (`lookoff.patch` in `2026-10-26-lookoff-exes`): arm A always takes a round's
  rival (`ABLATE=lookrival`), arm B its winner (`lookwinner`, no rival swap), against the lookahead's arm B of
  `2026-10-26-pool3-ab` (M 1672, held-out M 23897, job CPU 10019 s). Rival: M 1665, held-out M 23992 (+0.4%), job
  CPU 4007 s, below HEAD's 5451 (the lookahead also ran in HEAD's mines); free share .926/.796/.768/.708 against
  .926/.797/.768/.709. Winner: M 1702, held-out M 24534 (+2.7%), 4119 s. So rival swaps matter and the paths that
  check them do not, here; untested: the lookahead off with the two-variable pool, where it was added ("The cold loss
  is a greedy path loss").
- **Kept: the pool over three variables, `lt` too, and no lookahead (6078bfd, 411aacf; run `2026-10-26-keep-ab`, 38 min
  untimed, JOBS=3).** `POOL_VARS = 3` (`Pool` in `miner.rs`); `lt` patterns over three as well (the index's working
  set is about 105 MB: peak working set per process 334-356 MB in lookoff-ab's rival arm, 441-452 here); a round takes
  its rival when the rival gains more and proves, else its winner. Against HEAD 23b89fa: M 1718 to 1665 (-3.1%),
  held-out M 25675 to 23992 (-6.6%, lower on every salt), free share .926/.796/.768/.708; work counts (interp) 0.76x;
  job CPU 6719 to 5206 s under 40-68% other load. Every mine's results equal lookoff-ab's rival arm, so `lt` over
  three variables chose no new rule on these salts; it stays because it removes a special case.
- **At the loops' width, every-input proofs prove every `shr1` rule the oracle admitted (run `2026-10-26-blast-spike-run`,
  81 s; spike, `blast.patch` in `2026-10-26-blast-spike`, reverted).** The loops prove at width 4 (`miner.rs`, `laws`),
  so the oracle's exhaustive check decides a rule there; the spike turns it into a kernel proof: per output position, a
  case split over all k x 4 input bits whose leaves the kernel checks by evaluation (`lemma_n`, a Bool claim, since the
  split's motive is Type1 and a vector equality is Type2), joined by `cong_n` (`k_var_law_to`), any operator alike.
  On the 219 distinct `shr1` rules in the oracle arm's final rules (`2026-10-25-shr1-oracle`): all 219 check, 199 of
  them beyond the current `Prover` (with no mined rules); build and check per rule by variable count k: k 1, 30 rules,
  under 0.01 s; k 2, 27, 0.02 s; k 3, 160, mean 0.41 s, max 0.74; k 4, 2, mean 7.1 s (about 16x per variable, as the
  2^(4k) leaves predict). False rules fail (two hand cases). The mines prove only their winners, lazily (`400 provable
  candidates of 400 proposed`, filter 0.0 s), so as `Prover`'s fallback it would cost about 0.4 s per `shr1` winner
  over three variables. It proves at width 4 only: the loops' width, not the JIT's.
- **Kept: the every-input fallback (ab6f4a7; run `2026-10-26-everyinput-ab`, 32 min untimed, JOBS=3, arm A from
  `ARM_CACHE`).** `prove_rule` (`rewrite.rs`) tries its routes, then, for a rule of at most `EVERY_INPUT_BITS` = 12
  input bits (three variables at width 4), the spike's every-input proof (`every_input_law`). Against 411aacf: M 1665
  to 1562 (-6.2%), held-out M 23992 to 21905 (-8.7%, lower on every salt; the oracle's was -8.2% on the older baseline,
  "Even free `shr1` rules cut M by only 6%"), free share .942/.820/.787/.718 (1.0 to 2.4 points above 411aacf per band); work
  counts (interp) 0.74x; job CPU 5206 to 3860 s; final rules 1660 to 1904, those with `shr1` 93 to 350; peak working
  set per process 437-452 MB, unchanged. 0 of 20 arms failed. Making it the only rule prover is parked on cost
  (`PARKED.md`, "The every-input proof as the only rule prover").
  - *What it leaves unproved, and what false rules cost (2026-10-26, from the same run's mine logs and the admission
    test).* Lazy proofs of winners over the 60 mines: arm A 1664 proved and 1119 failed (554 rollbacks), arm B 1890
    proved and 2 failed (2 rollbacks), so the fallback also removes nearly all rollbacks. Both of B's failures are
    over four variables (16 input bits, past the cap): `sub(shr1(xor(x, y), 0), sub(z, u)) -> sub(u, sub(z,
    xor(shr1(y, 0), shr1(x, 0))))`, true, and `and(sub(or(x, or(y, z)), u), u) -> and(sub(or(y, or(and(u, x), z)),
    u), u)`, false at width 4 (336 of 65536 inputs, for example x 2, y 0, z 0, u 5) yet past the screen. So `shr1`
    rules past 12 bits cost one winner in 60 mines here. Rival proofs (`best_rival`, logged since b302e25; run
    `2026-10-26-rivallog-ab`, an A/A against ab6f4a7, rules the same in 30 of 30 loops): 64 proved and none failed
    over the 60 mines, under 0.05 s a mine. Of the 331 distinct winners whose proofs failed in either arm, 330 are
    true at width 4 (every one with `shr1`, 4 over four variables) and one is false, the rule above: a replica of the
    screen (`ValueMemo::screen`'s 204 inputs at widths 1-4; script `scr.py` in the rivallog run folder) passes it.
    With 0.51% of the width-4 inputs wrong, 202 random tuples miss it with probability about 0.995^202, 35%; pool
    candidates (up to three variables) are checked on every input (`ValueMemo::exhaustive`), cross-side candidates
    over three or four variables only on the screen. One false winner in about 4700 proofs costs one rollback. False rules are cheap to refuse: `rule_admission_refuses_wrong_rules` (465 false rules, at most four
    variables at widths 3 and 4) takes 0.18 s with the fallback and 0.00 s without (`EVERY_INPUT_BITS` 0), about
    0.4 ms each. The other callers of `prove_rule` (`rewrite.rs` `LawKind::Rule`, `search.rs`'s benches and tests)
    prove rules known to hold.

  - *What a rollback costs (2026-10-31, from logs already on disk, no code; `docs/runs/2026-10-31/scripts/rollback_cost.awk`).*
    Over the 3850 mine logs under `claude-runs\tatic` newer than 2026-10-28: 324 (8.4%) have a rollback, 391 rollbacks in
    all. Replaying the log's round lines, a rollback to round r voids the rounds r.. played so far, 3.9 rounds on average
    (1510 in all), 315 s of 70516 s of round time (scoring plus rule-set evaluation): 0.45%, about 0.8 s a rollback. The
    mine is 44% of a sweep's samples, so a rollback is under 0.2% of a sweep, and the 5.4% failure rate across all eras
    (48379 of 902050 lazy proofs) is probably mostly the old arms without the fallback (inference; the per-era split was not run). Left out: the failing proof's own time and the
    speculative proof threads' contention with scoring. The instrumented sweep is not worth running.
### Held-out M and transfer for v0.5 (2026-10-26)
- **What held-out M is made of now (run `2026-10-26-held-now`, about 2 min; `held_now.sh` in its folder, the
  2026-10-25 probe's script on arm B of `2026-10-26-everyinput-ab`).** Salts 1-3, loops 1-3, every band; each
  check's M equals the gate's `held_bands.txt`. Against the same probe on the 2026-10-24 baseline ("Where a loop's
  definitions should come from", above), per band 11/13/15/17: laws left to a whole-term machine proof 432/1286/1614/2165
  to 385/1193/1421/1975 (-9.5% in all), laws not proved 234/631/666/675 to 93/399/451/483 (-35%). So 78% of held-out M
  (4974 of 6400) is now machine-proved laws, 62 of them with `shr1`: the mined rules' reach on laws without `shr1`,
  not a prover, is most of what is left. The probe's sources (1) and (2) predate this split; the size-cap probes
  above (pool, cross-side caps) measured loop stragglers, not held-out laws.
  The laws not proved (run `2026-10-26-unproved-kinds`, seconds; `unproved_kinds.py` in its folder, classing the
  straggler lines of `2026-10-26-held-oracle`, below, by why `machine_fallback` fails): 1424 of the 1426 keep `shr1` in
  their normal form, each beside `add` or `sub`, so `Machine::parse` refuses them; the other 2 (band 17, `shl1` over
  sums, 4 and 7 and 5 and 8 carries) fail the carry-encoding search, and none is over the carry cap. They are 251
  distinct laws (17/69/75/90 per band, 85 of them unproved in all 9 loops) of the held-out files' 1302 laws with `shr1`
  (265/347/354/336). A prover that knows `shr1` would turn them into machine-proved laws and leave M as it is, since M
  counts both; only rules that settle them lower it.
- **What the loops see of the held-out laws (run `2026-10-26-held-overlap`, 12 min; `overlap.sh` in its folder, test
  `probe_held_overlap` in `deepextras.patch`, `2026-10-26-deepextras-exes`, reverted).** Per salt 1-10, the 900 laws
  the loops serve (phases 1-3, the first 300 each) and the 1650 the extras are drawn from (phase 0), against each
  held-out band. Exact copies are rare: on salts 2-10 the served laws hold 29 band-11 and 13 band-13 held-out laws in
  all (none of 15 or 17), about 3 per band and salt; the extras' source 0-14 per salt, again only in bands 11 and 13.
  Twins (the same twin key: renamed, children made canonical) are not rare: 38-85 served laws per band and salt are
  twins of a held-out law, 2467 of the 9000 served over the ten salts (27%), salt 1 as much as the others (its exact
  copies were dropped, its twins not), and every band has them, 17 included (38-56 per salt); 71-165 per band and salt
  of the extras' source. Counted per loop law, not per distinct held-out law. Both arms of an A/B see the same laws,
  so a gate's difference stands; the absolute held-out M and frontier include laws whose twin the loops served.
  (PARKED, "Drop the served laws' twins from the held-out set".)
- **Rules mined on the held-out laws themselves (run `2026-10-26-held-oracle`, 51 min; `oracle.sh` in its folder).**
  For the same 9 loops and every band, the miner as the loop runs it (`RULEMINER_FAST=1`) on the whole held-out band
  file with the loop's final rules as base; its stragglers are exactly each loop's held-out M (478/1592/1872/2458).
  Covered in-sample, per band 11/13/15/17: .98/.73/.61/.50, with 401/938/872/775 rules of which 338/782/710/567 fix
  at most one law when chosen. Uncovered with `shr1`: 8/175/201/213. Bands 13-17 hit the candidate cap (400) in all 27
  mines, which the loops' own mines never reach, so those shares are lower bounds. On one band-17 mine (salt 1, loop 1;
  `xcap-b17` in the folder, `xsize.patch` in `2026-10-26-xcaps-exes`, reverted): with the candidate cap lifted, 174 of
  272 at the cross-side cap of 13 nodes (536 candidates) and 246 at 17 (954); either way the laws fixed by rules that
  fix at least two are about the same (119 and 113), and the rest of cap 17's gain is 139 rules that fix one law each
  (61 at cap 13), 67 of them with a left side over 13 nodes. So larger size caps, the only reach an abbreviation can add, buy one-law rules here;
  whether those carry to unseen laws is the next bullet.
- **They do not transfer (run `2026-10-26-xfer-split`, 30 min; `xfer_split.sh` in its folder).** Salts 1-3, loop 1,
  bands 13/15/17: each held-out band file split into its odd and even laws, each half mined (as above, no candidate cap,
  X.exe at cross-side caps 13 and 17) and M checked on both halves. Summed over the 18 mines per cap (base M 1951 per
  side), the mined half's M falls to 652 at cap 13 and 219 at cap 17, but the other half's to 1614 and 1610: the same
  transfer (337 and 341, 17%; per band 64/116/157 and 71/122/148). Of that, the rules that fixed at least two laws when
  chosen carry 246 and 231. Cap 17's extra 433 in-sample points are one-law rules that fit their own laws only, so a
  definition that relieves the size caps would not lower held-out M; what transfers is the multi-law rules, which cap 13
  already reaches. Mining on half the held-out laws lowers the other half's M by 17%, rules the loops' own mines (on the
  laws they serve) do not find.
- **Fresh laws of the held-out sizes do as well (run `2026-10-26-fresh-transfer`, 12.5 min; `fresh.sh` in its folder,
  `F.exe` and `fresh.patch` in `2026-10-26-fresh-exes`, reverted).** The first v0.5 probe: is the split's 17% closeness
  to the held-out files, or what any laws of those sizes teach? 500 laws per band 13/15/17 from the stream sequence at
  another salt (8888888, each band's own growths as its held file), minus salt 1's served laws and the held files' own
  (148/12/0 dropped), mined as in the split (loop 1 of salts 1-3, its rules as base, no candidate cap, cross-side cap 13).
  Held-out M on the whole band files falls 521/619/811 to 463/469/598: -11%/-24%/-26%, -22% in all (1951 to 1530),
  against the split's 17% at the same cap. So the loops miss these rules because they never serve laws this large,
  not because the rules fit the held-out files: band 13, inside the loops' sizes, gains least. In-sample the mines
  cover 61-96% of their stragglers (b13 about 95%, b17 about 64%), at 51-83 rules each, 7-18 of them fixing two laws or
  more when chosen.
  - *Dose* (run `2026-10-26-fresh-dose`, 3 min; `dose.sh` in its folder): the first 100 and 250 of the same fresh laws
    per band, mined and checked the same way. Held-out M falls 6.4% at 100 laws per band, 12.7% at 250 and 21.6% at
    500 (1951 to 1827, 1703, 1530; per band 13/15/17: 3/12/4%, 5/19/13%, 11/24/26%), about 0.7 of M per mined rule at
    every dose (166, 347, 620 rules), so the gain has not levelled off by 500. Mining cost grows faster than the laws:
    summed over the three loops, 38 s at 100 laws per band, 136 s at 250, 546 s at 500 (band 17: 15, 72, 325 s).
  - *Chained batches* (run `2026-10-26-fresh-chain`, 10 min; `chain.sh` in its folder): 1000 fresh laws per band
    (its first 500 byte-identical to the 500 above) cut into four batches of 250, each mined with the loop's rules plus
    the earlier batches' as base, as a loop would. Held-out M after each batch: 1951 to 1703, 1543, 1454, 1411 (-12.7%,
    -20.9%, -25.5%, -27.7%); the batches gain 248, 160, 89, 43 at 347, 316, 215, 227 rules, so the gain per rule falls
    from 0.7 to 0.2 by the fourth. Two chained batches match one 500-law mine (1543 against 1530) at 231 s of mining
    against 546. Per band after the four batches: 13 521 to 392 (-25%, still falling: 437, 413, 392), 15 619 to 423
    (-32%), 17 811 to 596 (-27%, flat after the second batch: 617, 598, 596). So about 500-750 large laws per band take
    most of what this miner learns from them, in batches of 250 at 22-43 s of mining per loop and batch (all three bands).
  - *As the loop's extras* (run `2026-10-26-bigextras-ab`, gate salts 1-3, 24 min; `bigextras.patch` and `X.exe` in
    `2026-10-26-bigextras-exes`, reverted; A is `R.exe` from the arm cache): the first prototype of v0.5's loop change.
    The extras' source became the first 1650 laws of bands 13/15/17 of the sequence at 4 growths, minus every held-out
    law (salt 1: 427/653/570 per band, 108 held-out laws dropped), in place of phase 0 of the loops' 2-growth sequence;
    slices and share unchanged (salt 1 loop 1: L 1266, n 202). Held-out M 6400 to 6087 (-4.9%; per salt -6.5%, -2.1%,
    -6.1%), loop M 477 to 463, rules 580 to 674. Per 1000 laws by band: 11 53.1 to 61.6 (worse: the small extras it
    replaced taught band 11), 13 177.1 to 171.5, 15 208.6 to 191.8, 17 274.8 to 253.7; bands 13-17 -6.6%, about what
    the dose probe gave 100 laws per band (-6.4%), so the gain is the dose's, not lost to mixing with the batches. Cost:
    job CPU 1245 to 2841 s, peak process 1.5 to 3.3 GB; the 4-growth sequence took 256-401 s per sweep (three B arms
    at once, 64-70% other load) and the loops' wall about doubled (424 to 805 s summed). By the work counts (WORK lines,
    summed over the salts), the driver's `interp` (building both sequences) went 43.9 to 124.5 G and the mines' 31.2 to
    52.6 G, their walk, match and op 2.1-2.7x: the 4-growth build is about 80% of the added `interp`, and the mines'
    rewriting work more than doubled with 202 large extras per loop.
  - *At every size, and at three times the count* (runs `2026-10-26-deep-ab` and `2026-10-26-deep3-ab`, gate salts
    1-3, run at once, 27 and 35 min; `deepextras.patch`, `D.exe` and `D3.exe` with `PROBE_EXTRAS=4950` in
    `2026-10-26-deepextras-exes`, reverted): the extras' source became the first laws of the 4-growth sequence at every
    size, minus every held-out law and its twins (181-188 dropped per 1650, 541-556 per 4950). At 1650 (sizes up to 11,
    13, 15, 17 about 250/360/530/510; L about 1170, n 186-191 per loop) held-out M 6400 to 6112 (-4.5%), loop M 477 to
    467, band 11 still 53.1 to 61.3: the old extras' small laws are not replaced by a sixth of the count. At 4950 (n
    635-639 per loop) held-out M 6400 to 5167 (-19.3%; per salt -18.7%, -19.8%, -19.3%), loop M 477 to 439 (-8.0%),
    rules 580 to 1104, and every band lower or level: per 1000 laws 11 53.1 to 54.4, 13 177.1 to 147.4, 15 208.6 to
    162.2, 17 274.8 to 212.1. Cost at 4950: job CPU 1245 to 7802 s (6.3x; 2660 s at 1650), work `interp` 3.1x and
    walk, match and op 11-14x: the mines' rewriting work, not the sequence, now dominates.
  - *Count and slicing* (runs `2026-10-27-xgrid-s1650`, `-s3300`, `-s4950`, `-f4950h`, `-f4950`, `-s9900`,
    `-f9900h2`, gate salts
    1-3, one after another, 11-79 min each; `xgrid.patch`, base `R.exe` at 8482070 and one exe per arm with its
    `.exe.env`, in `2026-10-27-xgrid-exes`, reverted; all sweep profile, so CPU is not comparable to the bullet above).
    The deep source as above, at four counts, and a second slicing: `PROBE_SLICES=fresh` gives each of a loop's two
    mines its own disjoint n laws, where `extra_slices` gives both the same n. Base held-out M 6400, loop M 477, job CPU
    589 s, work walk/match/op 1.53/4.77/1.06 G.

    | Arm | Laws per mine (distinct per loop) | Held-out M | Loop M | Job CPU | walk / match / op (G) |
    |---|---|---|---|---|---|
    | shared 1650 | ~190 (~190) | 6112 (-4.5%) | 467 | 1325 s | 2.94 / 10.34 / 2.54 |
    | shared 3300 | 399 (399) | 5564 (-13.1%) | 460 | 4355 s | 9.11 / 35.07 / 7.97 |
    | fresh 4950, f 0.08 | 319 (638) | 5291 (-17.3%) | 438 | 3103 s | 7.02 / 28.10 / 6.33 |
    | shared 4950 | 638 (638) | 5167 (-19.3%) | 439 | 6167 s | 16.97 / 67.92 / 14.57 |
    | fresh 4950, f 0.16 | 638 (1276) | 4885 (-23.7%) | 432 | 8897 s | 18.39 / 76.75 / 15.85 |
    | fresh 9900, f 0.08 | 688 (1375) | 4690 (-26.7%) | 431 | 8870 s | 20.10 / 87.25 / 17.53 |
    | shared 9900 | 1375 (1375) | 4567 (-28.6%) | 419 | 21388 s | 42.0 / 186.7 / 38.6 |

    Shared 4950 and 1650 reproduce the bullet above exactly (held-out M and walk), so the port is faithful. Distinct
    laws per loop drive held-out M more than laws per mine: fresh at f 0.08 gets 90% of shared 4950's gain at half
    its CPU, and fresh at 9900, f 0.08 gets 93% of shared 9900's gain (same 1375 distinct laws) at 41% of its CPU and
    45-48% of its work. Halving the laws per mine at equal distinct laws costs 2.4-2.7% of held-out M at both counts
    (5291 against 5167, 4690 against 4567; at 9900 worse on every salt, by 21-77). Fresh at 9900, f 0.08 against
    fresh at 4950, f 0.16 (about the same laws per mine and CPU, work 9-14% higher): 4690 against 4885, inside the
    arm noise below; the pool is not a variable of its own, since the source is a prefix of the sequence and the
    slices are taken from its start, so arms with equal n mine the same laws. Shared 3300 is dominated by fresh 4950, f 0.08, and fresh 4950, f 0.16 nearly so
    by fresh 9900, f 0.08; the rest form the front. Gains keep coming with count (no plateau by 9900, where 1082 held-out laws or
    twins were dropped from L 8598). Fit over the seven arms (2026-10-28, from the run folders): an arm is set by its
    slicing and n; held-out M follows distinct laws per loop d, M = 9833 - 712 ln d (R2 0.975), and fresh slicing
    adds about +124-154 at equal d; along the fresh line M = 9761 - 769 ln n, with no knee: each halving of n costs
    about 530 M (8% of the base, 31% of fresh 9900's gain). Walk is linear in n above about 300 for the fresh
    arms, -4.28 + 0.0355 n G (mine 0, from no rules, -1.85 + 0.0244 n; mine 1 40% of that per law); the shared
    arms' extra cost is mine 1 re-reading mine 0's laws. Per-loop noise is about 33 M, so one 9-loop arm sum has
    about 100 M. Of a mine's search time 99% is join searches that fail, most reaching the 1000-term visit budget.
    Per 1000 laws, bands 11/13/15/17: shared 4950 54.4/147.4/162.2/212.1, fresh f 0.08
    53.9/150.6/165.6/219.8, fresh f 0.16 52.8/136.2/152.7/202.9, fresh 9900, f 0.08 46.6/129.8/148.3/198.2, shared
    9900 47.9/127.2/142.3/191.7: band 11 falls below the base's 53.1 only with 1276 or more distinct laws per loop.
    Peak process 5.1-6.7 GB (the 4-growth sequence built on 4 threads). The probe exes read the held-out files from
    the worktree path compiled into them: run `2026-10-27-xgrid-f9900h` failed at once on every salt after that
    worktree was removed, and `-f9900h2` is its rerun.
  - *Landed: fresh slices of n = 319* (66a9810, `EXTRAS_N`; run `2026-10-28-land-n319`, gate salts 1-3, `R.exe` against
    `L319.exe` in `2026-10-28-land-exes`, JOBS=2, 39 min). The deep source and fresh slices of the grid's probe, with n
    set directly; shared slices, `STREAM_EXTRAS` and `GEN_F` are gone. Held-out M 5340 against 6400 (-16.6%), loop M
    440 against 477, job CPU 2921 s against 589 (5.0x), walk/match/op 7.12/28.21/6.35 G (walk 4.6x). Salts 1 and 3
    reproduce fresh 4950, f 0.08 exactly (n was 319 there; extras, rules and held-out M identical); salt 2 had n 317
    there and gives 1750 against 1701, inside the per-salt noise. Per 1000 laws, bands 11/13/15/17: 55.6/151.4/167.6/
    220.8 (base 53.1/177.1/208.6/274.8); free share .944/.849/.832/.779 (base .947/.823/.791/.725). The 4-growth
    sequence took 28.4 s on 4 threads per sweep process (salt 1), and peak process 5.1-6.2 GB.
  - *Cutting a mine short: the truncation ladder* (run `2026-10-28-ladder-f9900h2c`, 114 min beside the gates below;
    `docs/runs/2026-10-28/scripts/ladder.sh` under `R.exe`). Could a stop rule end a mine early for less held-out M
    than a smaller n costs? Offline: fresh 9900, f 0.08's 9 libraries (n 686-689 by salt), each cut without mining
    again, in choice order per mine, and each cut's held-out M from the gate's own check. A cut's cost is the mine
    seconds of the rounds that chose its kept rules (a lower bound: a stop rule still pays the sequence and serving).
    The last column takes a cut's share of mine seconds as its share of walk (no walk is counted per cut) and gives n
    at that walk on the fresh line (walk -4.28 + 0.0355 n G, 20.14 G at n 688) and the fit's held-out M there.

    | Cut | Rules | Mine seconds kept | Held-out M | Same walk on the n-curve |
    |---|---|---|---|---|
    | full (control) | 1332 | 100% | 4690 | n 688, 4737 |
    | drop0: rules fixing at least 1 straggler | 1057 | 84% | 4819 | n 600, 4842 |
    | m0: mine 0's rules only | 633 | 68% | 5482 | n 508, 4970 |
    | stop3: up to the third in a row fixing fewer than 2 | 357 | 45% | 5661 | n 377, 5200 |
    | drop1: rules fixing at least 2 | 328 | 43% | 5593 | n 365, 5223 |
    | stop1: up to the first fixing fewer than 2 | 265 | 37% | 6053 | n 329, 5305 |

    The control reproduces the arm's 4690. Every cut a mine could reach (m0, stop1, stop3) loses to a smaller n by
    460-750, past the arm noise of about 100: measured, fresh 4950, f 0.08 (n 317-319) got 5291 at 35% of this arm's
    job CPU and walk, where stop1 got 6053 at 37% of its mine seconds. drop0, a bound no stop rule reaches (a rule's
    fixes are known only once chosen), ties the curve. The gain is in the tail: dropping the 729 rules that fix
    exactly one straggler each (drop0 to drop1) costs 774, the 275 that fix none 129. A mine's late rules carry its
    held-out gain, so n is the lever and a stop rule is not. Not rerun on the n 319 libraries: the margins are 460-750
    against a noise of about 100, and the budget below is the cheaper lever.
  - *A join budget for the mines alone* (runs `2026-10-28-mjv-j500`, `-mjv-j250`, `-mjv-j100` and `-mjv-j250n688`,
    gate salts 1-3, `L319.exe` against one exe per arm in `2026-10-28-land-exes`: `mjv.patch` on 66a9810, where
    `MINE_JOIN_VISIT` sets `JOIN_VISIT` in each mine's env only, so the loops' serving and the held-out check keep
    1000; J100 and J250n688 are J250's bytes with their own `.exe.env`, the latter also `EXTRAS_N=688`; A arms reused
    from `-land-n319`; JOBS=2, 26, 21, 10 and 14 min, at 19-52% other load (the first two beside the ladder), so job
    CPU and work counts are the measures, not wall). Of a mine's search time 99% is failed joins, most at the budget
    (above). The n 688 arm's budget-1000 reference is fresh 9900, f 0.08 (run `2026-10-27-xgrid-f9900h2`, n
    687/686/689 by salt). Base without extras: held-out M 6400, loop M 477, job CPU 589 s, walk 1.53 G.

    | Mines' budget, n | Held-out M (salts 1/2/3) | Loop M | Rules | Job CPU | walk / match / op (G) |
    |---|---|---|---|---|---|
    | 1000, 319 (landed) | 5340 (1774/1750/1816) | 440 | 1037 | 2921 s | 7.12 / 28.21 / 6.35 |
    | 500, 319 | 5192 (1754/1691/1747) | 450 | 1088 | 1542 s | 3.16 / 13.21 / 3.33 |
    | 250, 319 | 5237 (1737/1690/1810) | 440 | 1152 | 974 s | 1.32 / 5.62 / 1.76 |
    | 100, 319 | 5166 (1730/1668/1768) | 447 | 1140 | 627 s | 0.36 / 2.01 / 0.83 |
    | 0, 319 (third round) | 5271 (1752/1761/1758) | 469 | 1134 | 534 s | 0.00 / 0.26 / 0.26 |
    | 1000, 688 (fresh 9900, f 0.08) | 4690 (1559/1516/1615) | 431 | 1332 | 8870 s | 20.10 / 87.25 / 17.53 |
    | 250, 688 | 4577 (1533/1492/1552) | 424 | 1389 | 1671 s | 2.98 / 14.15 / 3.94 |
    | 100, 688 (third round) | 4622 (1501/1495/1626) | 426 | 1475 | 1247 s | 0.80 / 4.78 / 1.79 |

    A lower budget in the mines costs no held-out M down to 100, and saves most of the mining. At n 319, 500, 250
    and 100 are lower than 1000 by 148, 103 and 174, against a noise of about 140 for a difference of two arms (1.4 x
    100), and lower in all nine salt pairs (three budgets by three salts); loop M is level (440-450). At 100 the job
    CPU is 21% and the walk 5% of the landed design's: held-out M -19.3% against the base at 1.06x its job CPU
    (landed: -16.6% at 5.0x), the walk 24% of the base's. At n 688, 250 against 1000 is -113 (lower on all three salts), loop M 424 against
    431, at 19% of the job CPU and 15% of the walk; against the base -28.5% at 2.84x its job CPU, and against the
    landed design -14.3% at 57% of its job CPU. Along n at 250 held-out M falls 5237 to 4577 for n 319 to 688, about
    860 per e-fold (769 at 1000): the budget lowers the n-curve's cost without flattening its gain. The mines choose
    5%, 11% and 10% more rules at 500, 250 and 100 (n 319), and 4% more at 250 than 1000 at n 688. A guess, not
    tested: a pair the join no longer meets within the budget stays a straggler, so a rule that shortcuts it now
    scores, and serving at 1000 keeps the shortcut ("Derivability prune": a derivable rule is a shortcut, not
    redundant). Per 1000 laws, bands 11/13/15/17, and free share: at 500 49.8/149.1/163.9/216.0, .950/.851/.836/.784;
    at 250 52.7/152.5/162.8/215.9, .947/.848/.837/.784; at 100 57.1/150.2/160.4/208.2, .943/.850/.840/.792; at 250,
    n 688 51.1/129.9/141.9/187.3, .949/.870/.858/.813 (budget 1000 at n 688: 46.6/129.8/148.3/198.2, .953/.870/.852/
    .802). Band 11 is the one band that gets worse, at 100 (55.6 to 57.1) and at n 688 (46.6 to 51.1); band 13 at n
    688 is level (129.8 to 129.9); every other band improves. With the mining this cheap, building the 4-growth
    sequence is a third of the job: 34.0% of a sweep's busy samples at 100 (salt 1, run `2026-10-28-mjv-prof`,
    samply on a debug-info build of the J exes' code, taken beside the next round's gate, so shares only; it repeats
    that arm's rules), and the loops' 2-growth build another 12.4%. The two builds run one after the other, 4 threads
    each, before any loop starts: 31 of the sweep's 56 s. Inside the 4-growth build, grouping (`pool_conjectures`)
    is 52%: its exhaustive width-4 value vectors 31 points, reallocating each term's group key 9.4 (the 4096-byte
    vector is copied, then one byte pushed), the rest in the frame and its inlined hashing of those keys. The
    open-law filter is 33% (`Classes::normalize` 27), and growth and sorting the rest. Frames in
    `docs/runs/2026-10-28/rows/2026-10-28-mjv-prof.txt`; what it means for a lazy build is in `PARKED.md`, "Build the
    stream sequence lazily". At 250 the build's share is lower, at most 23% by 4 threads times that arm's logged
    build walls (55.7 s over the salts; the walls vary 13.7-28.4 s with load).

    **Landed 2026-10-30** (the mines' `JOIN_VISIT` defaults to 100, `MINE_JOIN_VISIT` overrides; serving and the held-out check keep 1000). Gate on current `main`, salts 1-3, A = the same exe with `MINE_JOIN_VISIT=1000`, B = the default (run `2026-10-30-land-mine100`, untimed, JOBS=2, other load 94%, so counts only): held-out M A 5340 (1774/1750/1816), B 5166 (1730/1668/1768), the 2026-10-28 numbers to the unit; loop M 440 against 447 (145/150/145 against 145/153/149); job CPU 3561 s against 788 s (22%, against 21% then); op count 6.3 G against 0.82 G. Rules differ in all 9 loops (the budget changes what the mines find). Frontier per band (free share, loops' rules; A then B): 11 .944 / .943, 13 .849 / .850, 15 .832 / .840, 17 .779 / .792, table alone .762 / .693 / .635 / .602.

    A third round (runs `2026-10-28-mjv-j0` and `-mjv-j100n688`, set up as above: J0 and J100n688 are J250's bytes
    with `MINE_JOIN_VISIT=0`, and 100 with `EXTRAS_N=688`) tried budget 0, a mine with no join at all, and 100 at n
    688. Both lost salt 3 to a hang (below; fixed, and salt 3 rerun, which gives the table above its "third round"
    rows), so every arm is recounted here on salts 1-2 from its gate's per-salt lines (base: the A arm of
    `2026-10-27-xgrid-f9900h2`; bands per 1000 laws from the arms' `held_bands.txt`, the table-only lines left out;
    the script, `docs/runs/2026-10-28/scripts/salts.sh`, prints salts 1-2 then salts 1-3):

    | Mines' budget, n | Held-out M (salts 1/2) | Loop M | Rules | Job CPU | walk / match / op (G) | Bands 11/13/15/17 |
    |---|---|---|---|---|---|---|
    | base, no extras | 4170 (2037/2133) | 323 | 416 | 433 s | 1.06 / 3.34 / 0.75 | 50.7/174.3/204.4/267.9 |
    | 1000, 319 (landed) | 3524 (1774/1750) | 295 | 693 | 1980 s | 4.58 / 18.06 / 4.17 | 53.5/148.6/165.0/222.2 |
    | 500, 319 | 3445 (1754/1691) | 302 | 720 | 962 s | 1.97 / 8.40 / 2.14 | 51.2/148.3/161.0/215.6 |
    | 250, 319 | 3427 (1737/1690) | 296 | 748 | 603 s | 0.83 / 3.57 / 1.12 | 49.7/148.6/160.5/214.3 |
    | 100, 319 | 3398 (1730/1668) | 298 | 739 | 389 s | 0.23 / 1.28 / 0.54 | 54.8/148.0/157.6/207.7 |
    | 0, 319 | 3513 (1752/1761) | 319 | 734 | 320 s | 0.00 / 0.15 / 0.17 | 66.3/152.3/162.2/206.6 |
    | 1000, 688 (fresh 9900, f 0.08) | 3075 (1559/1516) | 294 | 878 | 5752 s | 12.92 / 56.93 / 11.31 | 45.0/127.0/145.8/196.5 |
    | 250, 688 | 3025 (1533/1492) | 285 | 899 | 1122 s | 1.90 / 9.05 / 2.55 | 50.8/128.5/138.6/188.0 |
    | 100, 688 | 2996 (1501/1495) | 287 | 968 | 626 s | 0.51 / 3.06 / 1.15 | 47.5/127.3/143.6/182.6 |

    Budget 0 is no better than 100, and probably worse. Its held-out M is level with the landed design's (3513
    against 3524) and above 100's by 115, on both salts but by 22 and 93, which is at the noise (about 115 for a
    two-salt difference: the 140 above scaled by the root of 2/3). The clearer signs are loop M, the highest at n 319
    (319 against 295-302, higher on both salts), and band 11: 66.3 against 49.7-54.8 at every budget from 100 to 1000
    (band 13 152.3 against 148.0-148.6), while band 17 is level with 100's (206.6 to 207.7). Dropping the join
    entirely (the walk falls below 0.001 G) saves only 18% of 100's job CPU (320 s against 389 s), since what is left
    is the sequence builds, serving, and the mines' own rewriting and scoring (the held-out check runs outside job
    CPU). So 100 stays the lowest budget measured to cost nothing, and "mines don't join" is not shown to be as good.
    Why the easy band would lose first is not measured. Nor does budget 0 extend the rise in rules chosen (734
    against 739 and 748 at 100 and 250, 693 at 1000), which the straggler guess above would predict; that guess
    stays untested.

    At n 688, 100 holds: held-out M 2996 against 3025 at 250 (salt 1 lower by 32, salt 2 higher by 3) and 3075 at
    1000, loop M 287 against 285 and 294, at 56% of 250's job CPU and 11% of 1000's. Against the base it is -28.2% at
    1.45x its job CPU on these salts (100 at n 319: -18.5% at 0.90x; 250 at n 688: -27.5% at 2.59x; landed: -15.5% at
    4.57x), and against 100 at n 319 it is -402 at 1.61x. Along n, 319 to 688 lowers held-out M by 402 at both 100
    and 250 (449 at 1000): the budget keeps the n-curve's gain. The mines choose 8% more rules at 100 than at 250 at
    n 688, where at n 319 the two are level (739 and 748). Band 17 is the lowest of any arm (182.6); band 11 is 47.5
    against 45.0 at 1000.

    The hang. On salt 3 one mine of each arm went silent, its thread busy, until stopped by hand 1 h 53 min (budget
    0) and 1 h 28 min (100 at n 688) after its log's last line, and the arm failed. Rerun alone on a debug-info build of the same code (runs
    `2026-10-28-hang-j0` and `-hang-j100n688`, `docs/runs/2026-10-28/scripts/hang_probe.sh`), each hung again: a
    mine thread passed 120 s of CPU within 4 minutes of the start, where a whole salt takes 46-62 s of wall. 40 stack samples of the spinning thread
    (`stack_sample.ps1`, no debugger) put all 40 inside `embeds`' code (38 named `embeds`, 2 its inlined `Term::node`)
    and all 40 under `rewrite` called from a mine's
    `Scorer::score_laws` (frames in `docs/runs/2026-10-28/rows/2026-10-28-hang-j0.txt` and `-hang-j100n688.txt`).
    `embeds` (`crates/church-bv/src/rewrite.rs`) is the cycle cut's homeomorphic-embedding test, run by `cut_at` against
    the terms on the rewrite path (before the fix only those no larger than the term at hand), innermost first, both
    for the cut itself and for the memo's check of a cached result. It recursed
    both on "match at this node" and "skip a node of t", with no memo and no size check inside the recursion, so one
    pair of subterms could be reached along exponentially many paths. The terms compared are deep: the last sample of
    each rerun holds up to 138 (budget 0) and 496 (100 at n 688) nested `embeds` frames, each one node further down
    `t` (stale stack words count too, but the per-sample counts are steady), so these configurations, on salt 3,
    reach a rewrite over a hundred nodes deep where the recursion blew up. No sweep at the landed configuration had
    hung (the landing gate's three salts and the other 12 salt runs of the first two rounds, `-mjv-j500` and
    `-mjv-j250` then `-mjv-j100` and `-mjv-j250n688`, passed), but the code was on main.

    The fix (a5cb874, 9c09edf). `embeds` decides each pair of subterms once, in a map per top-level call, and settles
    a pair by size: no term embeds in a smaller one, and between terms of equal size embedding is equality (pointer
    equality, since terms are hash-consed). A call now takes at most |subterms of `s`| x |subterms of `t`| steps.
    Most calls are settled by size before any map is made, which keeps the memo's cost down: with a map for every
    call `embeds` was 1.64% inclusive of a sweep's busy samples, with the size test first 0.51%, against 1.76%
    before the fix (100 at n 319, salt 1, runs `2026-10-28-embeds-prof`, `-embeds-prof2` and `-mjv-prof`; shares
    only, all taken under load; frames in `docs/runs/2026-10-28/rows/`). Answers are unchanged: a unit test compares
    it with the old recursion on all 5.9 M pairs of terms over ADD and AND up to sizes 5 and 7
    (`embedding_matches_the_plain_recursion`), another needs an answer within 10 s on a pair of chains of one
    operator that the old code did not give (`embedding_long_chains_finishes`), and each loop chooses the same rules
    as the old code's run of the same arm and salt (salt 1 at 100, n 319 and n 688). Salt 3 of both arms then ran
    through (runs `2026-10-28-mjv-j0f` and `-mjv-j100n688f`, the A arm reused): 132 s and 218 s of wall where the
    hangs had run 1.5-2 h. A profile of salt 3 at 100, n 688 (run `2026-10-28-embeds-prof-n688s3`, beside salt 1's
    `-embeds-prof-n688s1`) has 8% more busy samples than salt 1, `embeds` at 1.01% against 1.00% and `rewrite` at
    25.1% against 25.5%: no costly region is left.

    On salts 1-3 (the "third round" rows above) the round's findings hold. Budget 0 is above 100 by 105 (5271 against
    5166; by salt +22, +93 and -10), within the noise of about 140, with loop M still the highest at n 319 (469
    against 440-450) and band 11 still the worst (65.4 per 1000 laws against 49.8-57.1, free share .935 against
    .943-.950); it is -17.6% against the base at 0.91x its job CPU (0.74x on salts 1-2; its salt 3 ran at 87% other
    load). At n 688, 100 is above 250 by 45 (4622 against
    4577; by salt -32, +3 and +74), also within the noise, and below 1000 by 68, with loop M 426 against 424 and 431,
    and the mines choose 6% more rules than at 250. Against the base it is -27.8% (250: -28.5%) at 2.12x the base's
    job CPU, but salt 3's job CPU is inflated by load: it ran at 80% other load and took 621 s, against 299 and 327 s
    for salts 1-2 (250 at n 688: 549, 573 and 549 s; budget 0's salt 3 took 214 s at 87%, against 156 and 163 s). The
    work counts don't depend on load: at n 688, 100's op count is 45-46% of 250's and its walk 26-28% on each of the
    three salts, so salt 3 costs no more at 100, against 250, than salts 1-2 do, and the salts 1-2 job CPU ratio (56%
    of 250's) stands. Not measured: the budget without extras.

