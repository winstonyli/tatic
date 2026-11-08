### The join's speed: lazy steps, canonical orders and the store (2026-10-18 to 10-21)

*Lazy join steps, and sweeps in lanes (2026-10-18; runs in `docs/runs/2026-10-18/README.md`).* The join's survey
(`PARKED.md`, now "Cheaper join searches") ranked lazy neighbours first; a probe sized it, and with lanes the extras' cost
falls from 331-386 s to 99 s on salt 1's cold sweep, every rule file unchanged.
- **Probe** (run `2026-10-18-join-count`, `patches/join_count.patch` on 6e621ca, salt 6 `cold:cmp3d` with extras, CPU
  33-100% from other sessions): the first mine made 490628 searches, 816.5 s searching (307.6 s failed), and built 387M
  neighbours, 162M (42%) new and 224M (58%) a term its side had reached, at 649M spine rebuilds (1.7 per neighbour). An
  operator-invariant cut (a pair whose sides differ in an invariant no step changes) fired 0 times in every mine, so
  option 3 is out: only pairs equal on random inputs are searched.
- **Lazy join steps** (7ee55b3). Each interned term carries `sh`, a structural hash from its children's (`sh_op`), so the
  hash of a step's term follows from its match and place without making it (`subst_sig`, `place_sh`). `join_search`
  keys its seen sets by `sh` (a `HashTable`), checks a hit with `is_step` (the siblings along the place by address, the
  replacement against the pattern), makes only new terms and keeps each step as (term, place, step index); plans are
  built only on the met path, by matching again (`step_plan`). The steps come in the order `join_steps` gave them and
  the seen sets fill alike, so the search is the same: a test compared it with the old one (plans, examined terms,
  reached counts) on 300 pairs before the old one was deleted. Salt 1, 1 lane, CPU 6% and 17%, RTP off: cold loop
  seconds 324 to 148 (wall 331 to 154 s), and cmp3d 15-1's first mine 251.5 to 109.9 s searching; every rule file of
  the default sweep (`ABLATE=gen`) and the cold sweep (extras on) unchanged (`-lazy-join`, `-eager-join-ab`). The gain
  is about twice the survey's bound (35-40%). A guess, not profiled: fewer `Term::op` calls also mean fewer per-thread
  cache evictions, so fewer shared-table lookups and lock waits under the mine's 6 threads.
- **Lanes** (397dcf2). The driver ran a sweep's loops one at a time, though each stage reads only what earlier stages
  wrote. `sweep` now runs a stage's mines, then its loops, `SWEEP_LANES` (default 2) at a time (`run_lanes`), each lane
  with its own worker and lemma file, rows in the old order (since a4eda36, loop i on lane i mod lanes: a loop's rules
  take no history from its lane, below, but its lemma loads and work counts do; "Work counts as the gate's cost"). Salt 1 cold, eager join: 386 s at 1 lane, 236, 223 and 199
  s at 2; the default sweep (`ABLATE=gen`) takes 5 s either way. The lazy join at 2 lanes: cold 99 s (`-lazy-lanes2`).
  Timings use `SWEEP_LANES=1`.
- **A timing one-off.** One of the three 2-lane cold sweeps (`-lanes-check`) differed in one loop (cmp3d 15-2: rules
  62 against 58); the other two (`-cold-l2-repeat`) and two 1-lane sweeps (`-cold-repeat`) agree. A loop takes no
  history from its lane (`-loop-history`: its cmp3d loops give the same rules at 1 lane, 3 lanes and with
  `LEMMA_RECHECK=1`), and the differing loop's laws files are identical: its first mine chose differently from the same
  input. Lanes share only CPU time with each other, so the miner is sensitive to timing under load. Where is open
  (`PARKED.md`, "The miner's choices depend on timing"); the mine's join counts also differ by about 70 searches between
  runs with equal rules, the same number moving between searches and memo hits, consistent with per-thread memos.

*The timing one-off is the join memo's inexactness (2026-10-18; runs in `docs/runs/2026-10-18/README.md`).* The two
`mine_0.log` files of the differing loop first differ in how many candidates a round scored (132 against 133), before any
choice: gains differ, not proofs. A gain differs only through the memos, and which entries a scoring worker's memo holds
depends on which candidates it scored (a shared queue) and on when speculative proofs come back. With an exact memo that
history would not matter; the join memo is not exact by design (option 1 of `docs/decisions/2026-10-17-monotone-join.md`:
a met join is kept under rules added off its path).
- **The kept entries disagree with fresh searches** (run `2026-10-18-join-check`, `patches/join_check2.patch`: on every
  join memo hit, the search rerun under the rules in force). Salt 1 cold:cmp3d, 2 lanes: up to 65 flips (kept met, a
  fresh search fails at the visit cap) and up to 790 hits whose fresh trace differs from the kept one, per lane worker of
  about 100000 hits (counters per process). The 2026-10-17 check (230000 hits, no flips, the default sweep before the
  extras and the lazy join) did not reach these laws; it also did not compare traces, which steer `affected` and the bound
  as much as a flip does.
- **Thread count as a deterministic stand-in for timing** (run `2026-10-18-join-exact`, `patches/join_exact.patch`:
  `LOOP_THREADS` sets the loops' scoring workers, `JOIN_EXACT=1` keeps every examined term in a met join's trace, the
  exact miner). As built, 1 thread against 6 changes loop 15-2's rules (rules 62 against 58, M 17 both), the loop that
  differed under load; with `JOIN_EXACT` the thread count changes no loop. So the memo's inexactness is the whole cause
  here, and the exact memo makes the miner's choices independent of its scheduling. Its cost: 108 s against 66 s at 6
  threads (1.56M against 1.18M join searches); its rules differ from the inexact memo's in all three loops, M 29/17/31
  against 29/17/30 (one salt). CPU 10% at start, RTP off.
- **Fixed by a memo per candidate** (2026-10-18, runs `2026-10-18-exact-salts`, `-snap-salt1`, `-snap-salts`,
  `-snap-threads`). Over salts 1-10 the exact memo costs +84% wall for M 750 against 749. The scheduling dependence came
  from each scoring worker's memo carried across the candidates it took from the shared queue; scoring each candidate
  from an empty memo keeps M (749 in every loop over salts 1-10), costs no time, and makes the rules byte-equal at 1 and
  6 threads (salts 1, 5, 7) and across runs. Built: `search::rule_miner` scores every candidate from an empty memo,
  `RewriteMemo::absorb` is gone, and `LOOP_THREADS` sets the loops' scoring workers; the check is
  `docs/runs/2026-10-18/scripts/threads_check.sh`. Rules differ from the old miner's in 4 of 30 loops (5-1, 6-3, 7-3,
  10-3), so older cold rows are not reproduced byte for byte. The before/after record (run
  `2026-10-18-pcand-salts-record`, `scripts/salts_ab.sh`, the old miner at dc2102c against 2de4854, so the memo per
  candidate, the size bound and the tags together; salts 1-10, the arms' order alternated per salt, others' load 27-29%,
  RTP off): M 749 in both and equal in every loop; wall 1130 against 954 s (-16%), job CPU 7942 against 6289 s (-21%).
  Rules differ in 4 of 30 loops again, but not the same four (1-2, 5-1, 6-3, 7-3): the old miner's rules move from run to
  run. Options in `docs/decisions/2026-10-17-monotone-join.md`
  ("Survey 3").

*Profile of the lazy join (2026-10-18, run `2026-10-18-lazy-prof`).* samply over salt 1's cold:cmp3d loops at 1 lane
(e654360 with debug info; CPU 7% at start, RTP off; frames in `docs/runs/2026-10-18/rows/2026-10-18-lazy-prof.txt`,
named by `scripts/prof_named.py`). Of 358357 busy samples (about 4.4 cores over the 82 s run):
- `join_search` 82.7% inclusive; the miner's memo tests `Trace::touched_by` 6.1% and `RewriteMemo::filtered` 5.3%;
- `Term::op` 28% inclusive, nearly all from `place` (21.8%, making a new step's term): the shared table's mutex 8.5% self
  (lock, unlock, spin; no other caller) and node compares 10.7% (7.0% probing the table, 3.7% checking the thread's cache
  slot), so most new terms miss the per-thread cache and go to the locked table, where loads of cold nodes dominate;
- `match_pat` 19.4% inclusive (13.9% from `join_walk` matching rules at every position, 4.2% from `touched_by`);
- `subst_sig` 12.2% (hashing a step's term before making it; `sh_op` 6.6%).
The levers, by share: the interner's locked path (a lock-free table: entries are never removed, so lookups could read
without a lock), the join's rule matching (it already goes through `PatIndex`, by root operator and operand classes; a
deeper index such as a discrimination tree pays only if most `match_pat` calls fail, which is not measured), and terms
made for steps never expanded (the last layer's terms are reached but never searched from).

*Counts behind those levers (2026-10-18, run `2026-10-18-match-count`, `patches/match_count.patch`).* Salt 1 cold:cmp3d,
2 lanes, summed over every mine (CPU 41% at start, RTP off):
- the join's matcher fails on 60% of its 5.54G calls after `PatIndex`'s cut, and 59% of the 2.23G matches give a step over
  the size cap, found only after `subst_sig` hashes it (identity steps 0.8%); so about 84% of matcher calls lead nowhere;
- of 324M step terms built, 37% (119M) are ever expanded; the rest are only reached;
- `Term::op`: 1.14G calls, 73.5% the thread's cache, 26.2% hits in the shared table, 0.35% new nodes. The locked path is
  almost all lookups of nodes that exist, which a lock-free read serves.
Levers this measures: a lock-free table read (below); a size bound before matching (a rule `from -> to` grows a term by
at least `size(to) - size(from)` when every variable occurs on the right at least as often as on the left, so a match at a
position whose term is already too large for the cap could be skipped unmatched; parked in `PARKED.md`); and building a
step's term only when it is expanded, up to 63% of `place`.
Built (branch `lazy-view`, 22d9867, not on `main`): exact but slower (run `2026-10-18-lview-ab`, salts 1-4 against
`bv_riv`, others' load 40-53%, RTP off): rules and M equal in all 12 loops, job CPU 2963 against 3211 s (+8%, higher in
every salt), wall 432 against 456 s, peak memory per process about 50 MB lower. Making a step's term was cheaper than
`place`'s share suggested, since 73.5% of `Term::op` calls hit the thread's cache, while the unmade steps cost on every
comparison (a walk from the step's `from`) and in `seen` entries that carry the match inline (about 90 bytes against 30).
Profiled against `main` (runs `2026-10-18-lvprof` and `-mainprof`, `lazy_prof.sh`, others' load 38-41%; the same 897 k
searches reaching 232 M terms in both): `join_search` took 442 k busy samples against 406 k. The deferral did what it
should: `place` (14.9% of `main`'s samples, nearly all `Term::op`) is gone from the visit, and making the popped terms
costs back 7.3%. The loss is the seen tables' equality: 18.3% (`Reach::head` 13.2% self, `Reach::same` 4.9%) against
`is_step` and `is_subst`'s 3.1%. The recursive `head` builds an operator-and-two-reaches result at every node of both
sides, where `is_step` steps one pointer down a made term. With an equality as cheap as `is_step`, the visit and pop would
take about 47 k samples fewer than `main`'s, roughly a tenth of the join, an estimate from the two profiles, untested
(PARKED.md, "Build a join step's term only when it is expanded").
Tested and refuted: with the full `sh` compared first and the equality a loop down both paths (`lazy-view` 984bde2;
runs `2026-10-18-lview2-ab`, exact in all 12 loops, and back-to-back profiles `-lv2prof` / `-mainprof2`), the join still
took 441 k samples against 403 k. `At::same` is 15.0%: its check against a made term (`At::is`) alone is 5.2%, above
`is_step`'s 3.1%, and about 7% goes to making the pattern subterm where one step reaches its pattern while the two still
agree. The estimate above assumed an equality as cheap as `is_step`; an unmade entry cannot be, since confirming a
duplicate (58% of steps) walks both derivations, and making a term is mostly a thread-cache hit. Pattern-to-pattern
comparison without making either would recover at most the ~7%, about break-even.

*What the join's duplicates and term building are (2026-10-18, run `2026-10-18-dup-count`, `patches/dup_count.patch`,
counting only, salt 1's cold:cmp3d loops).* Of 907.5 M candidates past the filters, 577.4 M (63.6%) reach a term their
own side has; 130.4 M of those (22.6%, 14.4% of candidates) are the term the popped one was reached from, and 99.7% of
those at the same place, so they are the step that undoes the step before. The 329.0 M new terms average a spine of 1.80
nodes and a pattern of 1.62 operator nodes, so making them costs about 593 M spine and 532 M pattern `Term::op` calls;
36.8% of them are ever expanded, so the spines of the rest are about 375 M calls (32% of all 1.18 G). Two cheaper levers
than the lazy step follow: making a step's subterm but deferring only its spine (equality then compares the subterm by
pointer, as `is_step` does, which removes the ~7% of pattern making that sank 984bde2) bounds at those 375 M calls,
roughly 6% of samples by `Term::op`'s 20.5% in `-mainprof2`; skipping the step that undoes the one before bounds at the
14.4% of candidates' `subst_sig`, placed hash and lookup, a few percent of the join; both estimates, untested. `Term::op`
itself: 74.0% of calls hit the thread's cache, 25.7% find the node in the shared table, 0.3% insert; 236.4 M of the 307 M
misses (77%) found the slot holding another node, so they are conflict or capacity misses, not first sight. 2^18 slots
did no better than 2^16 on salt 6 (above, "The interner's per-thread cache"), which points at conflicts, or at a 2 MB
cache missing L2 (1 MB per core) as often as the shared table does; which one is untested (PARKED.md, "Cheaper join searches",
item (b): decided against).

*The three levers, tried (2026-10-19).* Shadow caches in `Term::op` (run `2026-10-18-cache-ways`,
`patches/cache_ways.patch`, counting only; its direct-mapped 2^16 shadow hit exactly the real cache's 872.7 M) split
the misses: at 512 KB, 2 ways hit 77.5% and 4 ways 79.7% against 74.0%; doubling to 2^17 slots hits 79.5%, and 2^18 or
2 ways over 2^16 sets 83.2%. So most misses are capacity, the same-size cache gains at most 5.7 points, and the 83% of
2^18 already bought nothing on salt 6: decided against. Deferring only the spine is on `main` (eabd8d5): a seen entry
holds its step and the made rewritten subterm (`Spine`), a candidate is compared against it down both paths with siblings
and the subterm by pointer and the pattern unmade (`Spine::is_step`), and a spine is made when the term is expanded or
meets. It is exact (files the same in every run below) and cheaper: against `bv_riv` (`main` before it) in two quiet
rounds (run `2026-10-19-spine-quiet`, others 10-20%, RTP off) job CPU 274.0 and 252.4 s against 290.6 and 312.3 s, wall
54.9 and 50.4 against 58.4 and 62.4 s; job CPU there tracked others' load by about 5 s a point, and corrected to 15% the
gain is about 4%. On a quieter machine (run `2026-10-19-spine-main-quiet`, 4 clean rounds, RTP off) it won job CPU in
all 4: at 3-5% others 229.5 and 212.8 s against 249.5 and 232.6 (-8%), at 11% 260.1 against 268.2, and about even in a
round where it ran under 16.5% others against 6.6%; median wall 48.8 against 50.9 s. Skipping the step that undoes the one before, on top of it (07e3416, dropped; kept as
`docs/runs/2026-10-19/patches/undo_skip.patch`), is exact but dearer: in the three rounds at 5-6% others (run
`2026-10-19-spine-back-quiet`) 239.1, 228.5 and 238.3 s against 227.2, 232.6 and 226.9 (median of the 4 clean rounds +4%).
Its test runs on every match before the cap and identity filters, and a walk to the reached subterm per expanded term,
which cost more than the signature and lookup it saved on 14% of candidates (unprofiled).

*Profile with the spine deferral (2026-10-19, runs `2026-10-19-spineprof` and `-mainprof3`, `lazy_prof.sh` back to back,
others 6% and 3%, the same 897 k searches reaching 232 M terms).* The visit fell from 96.9 k samples to 76.6 k (`place`'s
30.6 k gone), and making the popped terms' spines (`Spine::make`) costs back 14.0 k, so `Term::op` went from 17.9% to 11.4%
of busy samples. But the whole profile has 249.5 k busy samples against 241.1 k, and the walk outside the visit, the same
code in both, took 114.5 k against 104.9 k: this one-lane profile's noise is about as large as the deferral's net (about 6 k),
so it neither confirms nor contradicts the 8% of the quiet two-lane A/B. What is left of the join, by self samples:
`match_pat` 16.7% (inclusive 17.7%); `JoinEq::min_size` about 5.5% (`Term::size` 3.0% and `map_or` 2.5%, once per indexed
rule per walked subterm); `subst_sig` 7.7% inclusive; `PatIndex::get` 3.3%; the hash tables (the seen tables in the visit,
`examined` in the walk) a few percent between them.

*The size need in the index (2026-10-19, bce3407, run `2026-10-19-room-quiet`).* `JoinEq::min_size` is replaced by a
`Need` that each join index entry carries: a step that keeps every variable needs its growth from the room the cap leaves
above the subterm, any other its `size(to)` of the cap, so the walk sizes a subterm once and skips with one compare
without loading the step (test `join_need_skips_only_steps_over_the_cap`, 5 of 5 mutations killed). Exact (every run's
files the same), but no gain: salt 1 cold:cmp3d, 4 clean rounds at 8-12% others, RTP off, job CPU median 250.5 s before
and 258.0 s after, won 2/4 (-7.8, +18.4, -5.0, +8.8 s). The profile's 5.5% for `min_size` was not arithmetic that could be
saved; a guess, unchecked: it was the step's loads, which the doubled index entries (16 bytes from 8) now pay.

*Why the join's matches fail (2026-10-19, run `2026-10-19-match-fail`, `docs/runs/2026-10-19/patches/match_fail.patch`,
counting only).* Salt 1 cold:cmp3d: `join_walk` walked 1.44 G subterms, the index offered 5.63 G steps (44% skipped by
the need) and `match_pat` ran 3.17 G times, 31% matching. All 2.19 G failures are rules' (associativity and commutativity
patterns are one level deep, so the index's operand classes decide them). By the least depth where the pattern's shape
rejects the subterm: 969 M (31% of calls) at the grandchildren, 934 M (29%) nowhere (a repeated variable bound to two
different subterms), 270 M (8.5%) at the root and 19 M deeper. The index rules out the root and operand classes of an
operator subterm, so the root misses are leaf subterms offered every leaf pattern (the leaf list is not keyed by
constant). Grandchild classes in the index, worked out once per subterm, and the leaf list keyed by class would avoid 39%
of the calls; the repeated-variable failures need the bindings compared, which `match_pat` already does in O(1) per pair.

*The index down to the grandchildren (2026-10-19, fcef618, run `2026-10-19-match-fail-shape`).* `PatIndex` keeps one list
per class of term, and each entry the shape bits (`Term::needs`) the pattern needs at the root and at its two operands,
checked against the term's and its operands' `Term::shape`; this replaces the operand class masks and the unkeyed leaf
list, for the rule index and the join's alike (test `pat_index_offers_only_matches_down_to_grandchildren`; 4 of 5
mutations killed, the fifth, leaf entries' own bits, was redundant with the list and removed). The shape's side bits are
`% 53` but distinct within one operator, so the operand check is exact. Counted as above: `match_pat` calls 3.17 G to
1.93 G, index candidates 5.63 G to 3.23 G, the same 977 M matches, no failure left at a leaf root or the grandchildren,
and the sweep's files the same. Timed (run `2026-10-19-shape-quiet`, `quiet_ab.sh 1 8`, 8 clean rounds of 11 at 6-19%
others, RTP off): job CPU median 242.5 s before and 223.1 s after (-8.2%), won 8/8 (-6.8 to -31.8 s), wall 48.8 to 45.4 s;
every run's files the same.

*Profile with the finer index (2026-10-19, run `2026-10-19-shapeprof`, `lazy_prof.sh`, the same 897 k searches reaching
232 M terms; frames in `docs/runs/2026-10-19/rows/2026-10-19-shapeprof.txt`).* 234.2 k busy samples against
`-spineprof`'s 249.5 k; the walk 172 k inclusive against 191 k. `match_pat` is 14.9% self (34.9 k samples, from 41.7 k):
the failures it still meets are mostly a repeated variable's, which recurse through the pattern before the bindings
differ. The index's filter is now the second cost of the walk, 5.6% self (`PatIndex::get`'s `fits`, an `all` over the
three needs, short-circuiting). `Term::op` 13.0% inclusive, `subst_sig` 8.6%, `Spine::make` 6.2%.

*The filter without branches (2026-10-19, 7e4f037, run `2026-10-19-fits-quiet`).* An operand's shape has its own class's
bit, so its needs check its class and the root's needs only repeated them (the list is the root's class): entries keep the
two operands' needs, tested in one `(n0 & !sa) | (n1 & !sb) == 0`. Exact (every run's files the same) but no faster: 8
clean rounds at about 5% others, RTP off, job CPU median 206.8 s before and 207.3 s after, won 3/8 (pairs -12.3 to
+7.7 s). Kept as the simpler index. The profile's 5.6% for the `all` was the loads of the candidates and their operands'
shapes, which the test still needs, not its branches. (This run's medians are 16 s under `-shape-quiet`'s for the same
`bv_shape`: a quieter machine, so compare runs only within an A/B.)

*What a repeated-variable pre-check would save (2026-10-19, run `2026-10-19-rep-var`, `docs/runs/2026-10-19/patches/rep_var.patch`,
counting only, on 7e4f037).* Of the join's 1.93 G `match_pat` calls, 987 M are of patterns that repeat a variable, and
934 M of those (95%) fail only because the variable is bound to two different subterms. Those failures visit 4.15 G
pattern nodes, 52% of the matcher's 7.96 G (4.4 a failure, against 3.8 a match). A pre-check that walks to each
occurrence of the repeated variables and compares them would walk 2.92 G nodes over those 987 M calls (3.0 a call)
when it compares every occurrence; stopping at the first two that differ walks less, but at least two occurrences' depths
(at least 1 each). So it saves between about 1.2 G and 2.2 G node visits, 15-28% of the matcher's work and on the order of
2-4% of the samples, before its own branches and the 53 M calls it lets through, which pay twice. Not worth building
as a general pre-check.

*Which repeated-variable failures the index could reject (2026-10-19, run `2026-10-19-shallow-eq`,
`docs/runs/2026-10-19/patches/shallow_eq.patch`, counting only, files the same as `-match-fail`).* `PatIndex::get`
already loads the term's two operands, whose nodes hold the grandchildren. Comparing the subterms at each pair of
positions within depth 2 that hold the same variable rejects 917 M of the 934 M binding failures (98%), 48% of the
1.93 G `match_pat` calls; 961 M calls are of patterns with such a pair, so 44 M would still go on to match. Patterns
rooted at `op(x, x)` alone are 311 M (33%), so a flag for that shape alone covers a third. The pairs (at most 15 among the
six positions) fit a `u16` per entry, against a mask of which pairs differ, worked out once per subterm.

*Profile with the branchless filter (2026-10-19, run `2026-10-19-fitsprof`, frames in
`docs/runs/2026-10-19/rows/2026-10-19-fitsprof.txt`).* Taken on a loaded machine (CPU 60% at the start, 27% just before;
the join's searches took 76.9 s against `-shapeprof`'s 55.4 s on one lane), so 295.8 k busy samples compare with nothing;
shares only. The filter (`get`'s `fits`) is 4.7% self against the `all`'s 5.6%: most of its cost is the candidates' and
the operands' loads, as the A/B said. `match_pat` 13.9% self, `join_walk` 6.0%, `Need::skips` 2.3% (0.9%: the entry's
load charged to the next line read), `Term::op` 13.1% inclusive.

*The depth-2 pairs in the index (2026-10-19, run `2026-10-19-pairs-quiet`, commit 75d4b99).* Each `PatIndex` entry now
carries the pairs among [a, b, aa, ab, ba, bb] where its pattern has one subpattern (a repeated variable), and `get`
compares only the pairs some entry of the term's class needs, once per subterm. Files the same; job CPU `bv_fits`/`bv_pairs`
median 210.9/203.6 s, won 5/8, under 5-18% others with RTP off. The won count understates it: the arm run second in a
round took 6.7 s longer on average (7 of 8 rounds), and `bv_pairs` won all four rounds it ran first (by 7.0-16.2 s) and
was within -2.8 to +3.9 s in the four it ran second. Averaging the two orders cancels the position: 5.7 s less (-2.7%),
and every pairing of a first-run round with a second-run round is negative. Less than the 48% of `match_pat` calls
of 13.9% self (`-fitsprof`) would predict (6.7%): the rejected calls fail at the binding, so each was cheaper
than the average call. Kept. The counters (run `2026-10-19-match-fail-pairs`, 75d4b99 + `match_fail.patch`, files the
same as `-match-fail`) agree with the probe: `match_pat` calls 1.93 G to 1.01 G, binding failures 934 M to 16 M, depth-3
failures 18.7 M to 12.5 M, the same 977.2 M matches; 97% of the calls left match.

*Profile with the depth-2 pairs (2026-10-19, run `2026-10-19-pairsprof`, frames in
`docs/runs/2026-10-19/rows/2026-10-19-pairsprof.txt`).* Started after a minute under 20% CPU, but the join's searches
took 67.2 s against `-shapeprof`'s 55.4 s on one lane, so others came back: shares only, against `-fitsprof` (also
loaded). `match_pat` inclusive 14.9% to 8.0%, while `PatIndex::get` went 2.2% to 6.8% (its own 0.8% to 3.0%: `shallow`'s
grandchild loads and the `differs` loop, with `Option<Term>`'s `eq` 1.2%; `fits` 4.8% to 5.9%). So the pairs cost about
two thirds of what they save in the matcher, which is the A/B's 2.7%. Working `differs` out only when a candidate with
pairs passes the shape test would save part of that, unmeasured. What leads now: `join_walk` 72.2% inclusive (5.4% self),
`Term::op` 13.6% inclusive (the interner's `eq` 4.4%, `Cells::find` 4.6%), `subst_sig` 8.7%, `rewrite_memo` 7.3%,
`Spine::make` 6.7%, `sh_op` 5.8%.

*The pairs compared only once the shapes fit (2026-10-19, run `2026-10-19-lazy-quiet`, commit cadb700).* `get` compares
an entry's pairs only after its shape test passes, instead of working out which of the class's pairs differ for every
subterm. Files the same; against `bv_pairs` job CPU median 202.0/195.6 s, and over the two orders -5.0 s (-2.5%):
`bv_lazy` ran 11.8-14.4 s faster in the four rounds it ran first and 0.0-4.4 s slower in the four it ran second (running
second +7.6 s), so every pairing is negative; the won count alone said 4/8. Kept; with it the depth-2 pairs are about
5% less job CPU than `bv_fits`.

*Profile with the pairs compared lazily (2026-10-19, run `2026-10-19-lazyprof`, frames in
`docs/runs/2026-10-19/rows/2026-10-19-lazyprof.txt`).* Taken without waiting for quiet (CPU 28% at start, searches
71.7 s), so shares only, against `-pairsprof`. The index's frames now sit mostly in the filter closure, which inlines
`differ`: self 7.5% there and 0.9% in `shallow`'s closure, against 5.8% and 3.0% (`get` itself) before, so about 8.4%
against 8.8% in all; the A/B's 2.5% is more than that drop, so the saving is mostly outside the frames that hold it
(fewer branches mispredicted or loads made, unmeasured). `match_pat` 8.1% self (7.5%), `Term::op` 13.4% inclusive
(13.6%), `join_walk` 72.8% (72.2%), `subst_sig` 7.9%, `Spine::make` 6.5%: the order of what leads is unchanged.

*Both arms at once on separate cores (2026-10-19, run `2026-10-19-lazy-aa-together`, commit ba246fd).* `runs time
--together` runs a round's arms at once, each on its own half of the mask (3F and FC0: three cores each), the halves
swapping every round; `quiet_ab.sh` takes it through `QUIET_AB_FLAGS`. An A/A of `bv_lazy` over 8 rounds: all clean,
files the same, and the halves read the same (over the two parts -0.8 s of 281 s, part 2 +1.0 s). But it is not the
cheaper way to a verdict. Each run takes 44% more job CPU and 43% more wall than alone (about 4.9 busy threads per arm,
as alone, now on three cores and their SMT siblings), and the rounds differ by 3.2 s (1.1%) around each part order's
mean, against `lazy-quiet`'s 1.6 s (0.8%) around each run order's. A round takes 57 s against 80 s, but the mean over
the two orders needs about twice the rounds for the same error, so sequential rounds stay the default; the whole run
took 30 minutes against 69, the difference being the quiet waits, which `--together` does not need to change. Kept as an
option, unused, then removed (it is in ba246fd).

*A shorter quiet wait before each round (2026-10-19, run `2026-10-19-lazy-aa-q10`, inconclusive).* Over every
`runs.tsv` so far (`docs/runs/2026-10-19/scripts/noise_load.py`), a pairing's distance from its run order's mean
grows with the round's highest other load: RMS 1.6% of job CPU under 10% (39 pairings), 2.1% at 10-20% (29), 8-11%
above 20% (6), so `--foreign-max 20` stays. The lever left was the 60 s of quiet `runs time` waits for before each
round. An A/A of `bv_lazy` with `--quiet-secs 10` gave 1 clean round of 9 in 36 minutes and was stopped: a 10 s dip
does not predict a quiet round, others' load came back at 12-45% within the runs (job CPU 220-317 s against
`lazy-quiet`'s 196 s). The machine was busier than in `lazy-quiet`, which got 8 clean of 8 with 60 s, so this does not
compare the two waits; that would need both alternating in one session. The default stays 60 s.

*Where `Term::op` stands (2026-10-19, survey, no run).* Its 13.6% inclusive in `-pairsprof` is the thread cache's and
the shared cells' confirming load of a node (`m.node == n`: the interner's `eq` 4.4%, of it 2.2% in the cache hit and
2.1% in `Cells::find`) and `op`'s own 4.1%. The levers inside the interner are spent: the cache's misses are capacity
("The three levers, tried": 2 ways decided against, 2^18 slots no better), the shared table's reads take no lock, and
the tags already skip other nodes without a load. The confirming load is the node the caller reads next (its shape,
size or children), so it is moved rather than added. What is left is fewer calls: `Spine::make` (6.7% inclusive, spines
made on expansion or a meeting), the join's step making, and `subst_pat`; a count of `Term::op` calls by caller is the
next probe (below).

*`Term::op` calls in the join by caller (2026-10-19, run `2026-10-19-op-callers`,
`docs/runs/2026-10-19/patches/op_callers.patch`, counting only on 3f2265b, files the same as `-match-fail`).* The join
makes 787.4 M `Term::op` calls in salt 1's cold:cmp3d loops (1.18 G before the spine deferral). 532.0 M (68%) are new
steps' `subst_pat`, 1.62 a new term over the 329.0 M new terms, and 92.5% of them hit the thread's cache (7.4% the
shared cells); 201.1 M (26%) are spines made for 118.7 M expanded step terms and the met ones, 1.69 an expansion, and
only 66.4% hit the cache (33.0% the cells); 54.3 M (7%) are the join's other calls, 92.0% cache hits. Only 1.59 M calls
(0.2%) insert a node: nearly every term the join makes already exists. The cells' 110 M lookups are where a call is
dear, and spines are 60% of them. 63.9% of the new terms (210.3 M) are never expanded, so their `subst_pat`, about 340 M
calls (43% of all), is made only to be compared by pointer. Deferring it too is the lazy step that sank 984bde2, and
comparing entries unmade was put at about break-even ("Counts behind those levers"); with 92.5% cache hits these calls are the
cheap ones. The dearer calls are the spines' cell lookups, 66.3 M, which a larger thread cache did not remove.

*Subterms a search walks again (2026-10-19, run `2026-10-19-walk-repeat`, `docs/runs/2026-10-19/patches/walk_repeat.patch`
on top of `op_callers.patch`, counting only on d1599dd).* An expanded term is its parent with one path rebuilt, so
`join_walk` meets the subterms off the path again. Over salt 1's cold:cmp3d loops it was at 1436.2 M subterms, and 1181.6
M (82.3%) of them had been walked earlier in the same search; 596.5 M (59.3%) of the 1005.9 M `match_pat` calls were at
those (the new subterms are the path's, larger, with more candidates). A subterm's matches, and each match's
right-hand side `sh`, size and whether it rewrites to itself, depend on the subterm alone (the cap's room is checked per
visit from the stored `Need`; `PROVING` does not change within a search), so a per-search memo of them would skip the
index filter at 82% of visits and the matcher at 59% of its calls, with `subst_sig` and `is_subst` for those matches.
Those frames are about 30% of the samples in `-lazyprof`; a memo lookup costs one probe of a table of a few hundred
entries per search. Not built as such: see the next paragraph.

*The same subterms under one rule table (2026-10-19, run `2026-10-19-table-repeat`,
`docs/runs/2026-10-19/patches/table_repeat.patch`, counting only on 5aafba2).* A subterm's join matches depend on the
rule table, not the search, and a table serves 7.4 searches on average (166.7 k tables, from `set_extra_rules`, for 1.23 M
searches). Under one table 1239.6 M of the 1436.2 M visits (86.3%) were at a subterm already walked; a direct-mapped
cache by `sh` would hit 85.4% with 2^16 slots and 83.9% with 2^12, so a small cache keeps nearly all of it. The rewriter
does not need one: `rule_step_in` ran 14.5 M times, 1% of the join's visits, and 14.3% of those at a term it had seen
under the table. Clearing a cache per table would cost more than it saves at 2^16 slots (166.7 k clears), so a cache must
be invalidated by tagging, not clearing.

*A cache of the join's offers per rule table (negative, reverted, 2026-10-19, run `2026-10-19-offers-quiet`, commit 5997554).*
`JOIN_OFFERS` kept each subterm's index offers in 2^12 direct-mapped slots tagged by the table's id and an epoch, each
offer matched on its first visit within the cap and kept with its rewritten subterm's `sh` and size. The sweep's files
were the same, but against `bv_lazy` it cost +8.1 s of job CPU over the two orders (+3.6% of 221 s; +5.4 s first, +10.8
s second), won 1 of 4 clean rounds, wall +1.3 s, and +80-110 MB peak per process; only 4 of 8 rounds stayed under 20%
other load by the 3 h deadline, so the size is loose, but there is no gain. The 86% repeat rate did not turn into time:
what a hit skips (the index filter, one `match_pat` and `subst_sig` per offer) costs about what the lookup and the
96-byte offers it reads cost, so the ~30% ceiling read from `-lazyprof`'s frames was not there to take.

*The join's frames again, after the offer cache (2026-10-19, run `2026-10-19-lazyprof2`, shares only, under load).* A
fresh profile of the same code read within 0.5 points of `-lazyprof`: `join_walk` 73.1% inclusive, of which its visit
34.3% (`subst_sig` 8.0%, the reached sets' `find` 6.7%, `place_sh` 2.9%, `Spine::is_step` 2.3%); outside the visit the
index filter 9.2%, `match_pat` 9.0%, `join_walk`'s own 4.6%; `Term::op` 12.1% across the join (`Spine::make` 5.8%,
`subst_pat` 3.8%); the rewriter 7.3% and `set_extra_rules` 2.6%. The offer cache skipped about 85% of the index filter,
`match_pat`, `subst_sig` and `is_subst` (28.7% inclusive in all, so ~24% expected) and still lost 3.6%; likely (not measured) because its lookup reads
a slot and then offers in a 3 MB array at random, against index entries and interned nodes that stay in cache. The
shares of these frames measure work that was cheap compute, not time a memo can take; a lever on the join has to
remove visits or memory traffic, not recomputation.

*Where the offer cache's time went (2026-10-19, run `2026-10-19-offersprof`, 5997554 profiled, shares only, under
load).* Against `-lazyprof2` the cache took `match_pat` under `join_walk` from 7.7% to 4.8%, the index filter from 9.2%
to 5.3% and `subst_sig` from 8.0% to 3.7%: about 11 points, not the ~24 the hit rate promised, because the hits are at
the small subterms off the path, where matching was cheap, and the misses at the new path subterms carry most of it
(`match_pat` at the walk's root, never a hit, stayed at 2.2-2.4%). It added about as much: `JoinOffers::at` 12.0%
inclusive, 6.7% beside the index it calls on a miss, the walk's loop closure 2.8%, `Need::skips` and `Term` equality
+1.9 points. This replaces the memory-traffic guess above as the measured account: the saving was half the estimate
and the lookup ate it.

*Canonical orders for the join search: overview (2026-10-19/20; the dated paragraphs below hold the measurements).*
`join_search` reaches the same term by commuted orders of the same steps. A canonical order skips those repeats after
each step. Its test is the gate: the same mined rules in all 15 loops of salts 1-5. That test is strict. The greedy
rule picks diverge at the first near-tie after any change, so the join's answers and its trace (the terms a result
rests on, which decide memoized reuse and which laws a candidate touches) must not move. The thread so far:
- Left-to-right order for disjoint steps (f6cb81c). Not exact at first: the skipped order's middle term could exceed
  the size cap. Made exact by the guard (0e1dab3): order the walk only after a step that did not shrink the term.
  This is committed, about 6% faster per search than no order.
- Inner first for nested steps (skip the bindings of variables once in from and to). It failed the gate alone
  (b7bb853, reverted). Under the guard it gave the same answers in 4.63 M searches but other rules: its met paths, and
  so its traces, differ from no order's.
- Traces no order changes. All were exact, and all cost more than the skip saves:
  - every reached term: 4.5x job CPU;
  - every shortest meeting path, found by a second walk: at least +39%;
  - one canonical path found by pair tests: +37% job CPU against left-to-right.
  Each needs the met layer finished (+10%) and a wider trace for failed searches. Inner first alone is about 5% per
  search ahead of left-to-right (-11% against -6% per search, two gates).
- Ruled out without building:
  - canonical parents: a term's parents depend on the order;
  - edges recorded in the forward walk: the skip drops the edges an order-free trace needs;
  - standardizing the met path (reordering its commuting steps into a normal form, as a standard reduction does):
    the first meeting term already depends on the order, so it still needs the finished layer, whose +10% alone
    exceeds inner first's 5%.
- Status: inner first decided against (PARKED); left-to-right under the guard stays.

*Independent join steps in left-to-right order only (2026-10-19/20, runs `2026-10-19-join-order`, `-join-order-pair`,
`2026-10-20-join-order-alt2`, `docs/runs/2026-10-19/patches/join_order*.patch`; built in f6cb81c).* Two steps at disjoint
places reach the same term in either order, and the search made it both ways. Walking a term a step reached without the
subtrees left of that step's path (its ancestors, its rewritten subterm and everything right of it still walked) keeps
one order. Run both ways on every search in one process, keeping the base's result: `join_walk` calls fell 28.3% (1436.2
M to 1029.4 M) and the reached terms 1.7%, and 4698 of about 1.23 M searches changed outcome, 2280 met only in the base
and 2418 only ordered: not the same search, as the cap and the visit budget cut the reordered paths differently, but
not a weaker one. With which runs first alternated, the ordered search took 29.2 s less over the two orders (about 21%
of search time; base first 155.7 against 99.1 s, ordered first 127.7 against 126.0 s; running second saves 27.5 s
either way), under 49% other load. Run alone it changes the mined rules, so its files differ; on salt 1 M stayed 29,
17, 30 per loop and the join closed 49/70/61 laws against 49/67/47.
The quality gate over salts 1-5 (run `2026-10-20-order-gate`, `docs/runs/2026-10-20/scripts/gate_sum.sh`) passes: M 363
before, 362 ordered (one loop 19 to 18, the other 14 equal), the join closed 848 laws against 825 (more on salts 1-3,
fewer on 4 and 5), and no law went unproved, exhausted or over the rule budget in either. The rule sets differ in every
loop, and with them the work: 8.62 M searches against 8.42 M (salt 3 +47%, three salts 9-19% fewer), so the job CPU
fell only 8.8% (2264 against 2482 s, under 22-48% other load), less than the paired probe's 21% of search time; time per search fell 6.4% (250 against 267 us), over other searches.
On a quiet machine the paired probe again took 20.9% less search time (226.5 against 179.2 s, run
`2026-10-20-join-order-quiet`), but end to end on salt 1 at 1 lane (`2026-10-20-order-quiet`, 8 clean rounds) the job
CPU did not move (216.4 against 216.7 s median, +0.2 s over the two orders): the ordered rule set ran 17.5% more
searches (1.45 against 1.23 M) at 17% less time each. The gain per search is real; whether it shows end to end depends
on which rules the order lets the miner keep.

*Where an ordered walk goes (2026-10-20, run `2026-10-20-walk-categories`, `docs/runs/2026-10-20/patches/walk_categories.patch`,
counting only).* Salt 1 with the ordered rules, by where each walked subterm lies relative to the step its term was
reached by:

| | walk calls | `match_pat` calls | matches |
|---|---|---|---|
| a side's own term | 23.4 M | 29.9 M | 29.2 M |
| an ancestor of the step | 221.0 M | 293.9 M | 258.8 M |
| the step's subterm | 129.3 M | 316.9 M | 312.3 M |
| inside it | 583.3 M | 212.2 M | 211.9 M |
| right of the path | 177.9 M | 71.1 M | 70.8 M |

Reusing the parent's matches right of the path (the same subterms, walked in the parent) would skip 8% of the matches'
work and 16% of the walk calls: too little to pay for carrying the parent's match lists, so not pursued. At the
ancestors, 185.3 M of the 258.8 M matches put the step under a variable of the rule's pattern (they do not overlap it),
and 157.9 M under a variable that occurs once in `from` and once in `to`: those two steps commute one for one, a diamond
the search still takes both ways, as it took disjoint steps before the order. Its other order is a step inside the
rewritten subterm, in the binding of that variable, and inside the subterm is where half the walk calls are.
Following the rule's `to` down the subterm (run `2026-10-20-walk-bindings`, `patches/walk_bindings.patch`, the same
rules): the bindings of variables once in `from` and `to` hold 399.9 M of the 1134.9 M walk calls (35%) but 90.9 M of
the 883.0 M matches (10.3%); the rest of the subterm 183.5 M and 121.2 M. Skipping them, as the left-of-path subtrees
are skipped, would cut more walk calls than the left-to-right order did (28%) but fewer matches.

*Nested steps inner first only: fails the gate (2026-10-20, run `2026-10-20-inner-gate`, b7bb853).* `JoinEq.once` marks
the variables once in `from` and once in `to`, and `join_walk` after a step skips their bindings in the rewritten
subterm (test `join_walk_after_a_step_skips_the_bindings_of_its_variables_once_in_from_and_to`). Against the
left-to-right order alone (f6cb81c), salts 1-5: M 362 against 365 (salt 1 loops 2 and 3, salt 5 loop 1, +1 each);
joined 848 against 808; exhausted, not proved and budget 0 in both. Per search the join is 11% cheaper (292.2 against
259.3 µs), but the rules it mines differ and run 17% more searches (8.62 M against 10.12 M; salts 1 and 5 +61% and
+65%), so job CPU rose 7% (2404 against 2571 s). The other order of each diamond is still taken, so
a search loses a join only where that order's middle term is over the size cap and the skipped one's is not
(unmeasured); the rest of the M and joined change comes through a different mined rule set, as with the left-to-right
order's +17.5% searches on salt 1. On a quiet machine (run `2026-10-20-inner-quiet`, salt 1, 8 rounds) the job took
51% more CPU (210.6 against 318.8 s median, won 0/8): 61% more searches at only 5% less each (about 114 against
108 µs), far below the gate's 11%, which was taken under load. Rerunning each of the skip's join searches without it
(run `2026-10-20-inner-probe`, `patches/inner_probe.patch`, salts 1 and 5, the two that lost M) shows the skip is not
what loses proofs: of 2.33 M searches on salt 1, 4492 met only with it (4470 of them because the unskipped search hit
the visit bound first) and 2770 only without it (1575 at an empty front, the cap stopping the other order; 1195 at the
visit bound); salt 5 7568 against 912. The skip meets more within the bound, and the M and joined losses come through
the different rules it mines, with their 61% more searches. Reverted (the commit after 5be9ad2): it costs 51% more CPU
for a worse M. Why more met searches mine worse rules is not known (unmeasured); once it is, the skip is worth retrying.

*How far a change to the join's answers moves the mined rules (2026-10-20, `scripts/first_diff.sh` on the gate runs,
and run `2026-10-20-visit-probe`).* The miner picks rules greedily by laws fixed and size saved, and a rule's score
counts the joins it allows, so any change to which searches meet changes the scores: the first rule of salt 1 loop 1
fixes 146 laws without the inner-first skip and 155 with it, and the picks part at rule 5. In both gates every loop's
cmp3d picks part within the first 18 rules of about 65 (left-to-right order: rules 1-14, median 4;
inner first: 1-18, median 3), so each arm mines a different rule set from there on. The two gates' per-salt swings in
searches are alike (left to right: salt 3 +47%, salts 2, 4 and 5 -9 to -19%; inner first: salts 1 and 5 +61% and +65%,
salts 2-4 -1 to -7%), and so are their M changes (-1 and +3 over 15 loops). A change that moves the join's answers is
therefore judged end to end against a rule-set lottery: a single salt (the 51% above) says little, and a gate over five
salts separates a real effect from the lottery only if it is larger than the spread a neutral change produces
(unmeasured; a visit bound of 1001 for 1000 would be one). What does not depend on the picks is each search's own
answer and cost, measured by rerunning the same search (the probe above). The visit bound moves far more answers than
the step order: under the left-to-right order, 9.4% of the 8.62 M searches over salts 1-5 end at the bound of 1000
reached terms, and at 4000 59% of those meet (476894, 5.5% of all searches; the skip's net gain was 0.07% and 0.3%); 2.7%
end at an empty front, a no within the size cap.

*Making the picks less sensitive (survey, 2026-10-20, nothing built).* A law covered is worth 1000 in a round's gain
against a few hundred of size, so one join answer flipped moves a candidate by a whole law, and later rounds' gains are
+1 to +3 laws: the picks part at the first near-tie the flip reaches. Two kinds of change flip answers. A real one (a
bigger visit bound, other rules) should move the picks, and is judged against the spread of a neutral change. A search
order should not: the walk's own doc says a canonical order reaches the same terms at each depth "except where the cap
stops the other order's middle term", and with the same terms per layer the visit bound (checked between layers) and
the meeting layer come out the same. The middle term of the order not walked is `size(t) - Δ + δ` where `Δ` is the size
change of the step that reached `t` and `δ` the skipped step's; the order walked ends at `size(t) + δ`, within the cap.
So when `Δ >= 0` (the step did not shrink the term) the other order's middle fits too, and the skip loses nothing; for
both skips (left of the path, and the bindings of variables once in `from` and `to`, whose step changes size by the same
`δ` in either order). Guarding the skip by `Δ >= 0` would make any canonical order exact: the same rules and M as no
order, checked by equal output instead of a gate, with the walk savings kept wherever steps do not shrink (unmeasured
share). Selection-side fixes were tried before and lost: held-out scoring, held-out runners-up, lookahead over runners-up
("The cold loss is a greedy path loss" and after); ties broken in bands would still move by a whole law per flip.

*The order made exact (2026-10-20, run `2026-10-20-guard-gate`).* `JoinStep::order` gives the walk its order only after
a step that did not shrink the term (test `a_join_step_orders_the_walk_after_it_only_when_it_did_not_shrink_the_term`).
Against no order at all (`bv_lazy`, f6cb81c's parent), salts 1-5: the same rules in all 15 loops, M 363 both, joined
825 both, the same 8424652 searches; search time 2499 against 2342 s (296.6 against 278.0 µs per search, -6.3%), job CPU
2486 against 2308 s (-7.2%), wall 346 against 362 s (26% other load at start, RTP off; one run each, not a quiet A/B).
So the order's cap losses were the whole of its change to the answers: the dedup of a term reached first by another
order's path loses nothing here. The unguarded order skipped more (-17% per search, quiet) but changed the rules, and its
M 362 against 363 was a pick of the lottery. A step-order change can now be checked by equal output.

*Inner first under the guard: the same answers, other plans (2026-10-20, runs `2026-10-20-guardin-gate`,
`-guardin-probe`; `patches/inner_guarded.patch`, not committed).* With the inner-first skip back on top of the guard,
the rules differ from no order in 4 of 15 loops (M 363 both; job CPU -10% under 41-45% load). Yet rerunning each search
without the skip (salts 1, 3 and 5) changed no answer in 4.63 M searches; only the number of terms reached differs, in
about half, which a met search's stop mid-layer explains. So the rules differ through something other than the answers,
most likely the met path (a guess, unmeasured): the walk matches a term's root before its children, so with no order a
search finds the outer-then-inner path first, and the inner-first skip removes that path and meets by the other. The
plan, and the terms its path examined, then differ; those terms are the join's trace, which decides where a memoized
join is reused under other rules (inexact by design, `RewriteMemo::filtered`) and which laws a candidate can touch. The
left-to-right order keeps the path walked first (left before right), so its plans did not change. The walk after steps
that shrank the term is 1.8-2.3% of walk calls and 1.3-1.6% of expansions, so the guard costs little, and narrowing it
(skipping there what the cap allows) would win back at most about 2% of the walk: not pursued.

*A trace no order changes: the guess confirmed, at about 4x the cost (spike, 2026-10-20, run `2026-10-20-canon-gate`;
`patches/canon_noorder.patch`, `patches/canon_inner.patch`, not committed).* `join_search` finished the layer it met in,
took the meet with the smallest (term `sh`, from `sh`, eq), and gave every search, met or not, the trace of all terms
reached on both sides with their subterms. These depend on no order, since an exact order reaches the same terms each layer. With
that change, no order and inner first under the guard mined the same rules in all 15 loops of salts 1-5, and both made
the same 19.25 M searches. So the plan and trace caused the divergence, not the answers. Inner first then
saved 19% of search time (8691 s against 10776 s) and 14% of job CPU (9303 s against 10840 s). But the change itself is
costly. Against the `guardin-gate` no-order arm, searches went from 8.62 M to 19.25 M (the larger traces cut memoized
joins' reuse) and from 292 to 560 us each (the finished layer, and making every reached term). Job CPU went from 2404 s
to 10840 s under 20-49% load. Most of the cost likely comes from the wider trace, not the canonical meet (unsplit). A
trace of the path alone would be cheaper, but the path runs through each term's first-found parent, which the order still picks.

*Where that cost goes, and a cheaper trace no order changes (spike, 2026-10-20, runs `2026-10-20-split-meet`,
`-split-trace`, `-split-exact`; `patches/split_spike.patch`, not committed).* Split, with no order in every arm but the
last. Finishing the met layer and taking the smallest meet costs little: 8.42 M to 8.00 M searches, job CPU 3089 to
3412 s (+10%) under 57-62% load. The wide trace is the cost: tracing every reached term made 18.08 M searches against
9.23 M for the cheaper trace in the same gate. Canonical parents cannot make the path's trace order-free. Inner first
removes some steps from a term's parents, so the set of parents, and the smallest among them, still depends on the
order. What no order changes is the union of all shortest meeting paths. Take the meeting terms of the finished layer at
the least depth on the other side, then, on each side, the terms of each layer below with a step into the union's terms
above. That needs a second walk of the met search's layers, in no order. A failed search's trace becomes the walked
terms with their subterms, since the skip leaves parts of a walk unexamined. With that trace, no order and inner first
mined the same rules in all 15 loops and made the same 9.23 M searches (`split-exact`, 14% load). Inner first then took
19% less search time (3437 s against 4238 s) and 16% less job CPU (3615 s against 4284 s). Against the committed code
the trace costs more than inner first saves. In this spike's no-order arms, 9.23 M searches against 8.42 M (+10%) and
a second walk per met search, so 4284 s quiet against 3089 s at 62% load: at least +39%. The left-to-right order,
committed and cheaper than no order, was not in these arms, so inner first with this trace has not been timed against
it.

*An order-free trace without the second walk (survey, 2026-10-20, not built).* There are two ideas.

First, record edges during the forward walk. This cannot be order-free. The walk at a term is ordered by the step that
first reached it (`r.step()`). The skip then drops exactly the edges a commuted path would use, and which edges it drops
depends on which parent came first. So any order-free trace needs the edges the pruned walk did not make. The skip is
also what inner first saves, so making those edges by walking again costs the saving back.

Second, test pairs instead of walking. A join step rewrites one subterm (`JoinStep`: `from`, `path`, `eq`). So whether
term `p` has a step to term `m` can be checked without a walk: descend while the two agree at the root and in one
child, then match `join_index` at each node of that spine against the other side's subterm there. That is a handful of
pattern matches per pair, against a full walk of `p`. With pair tests, the backward pass can also keep one canonical
path instead of the union: the smallest-key parent with a step into each term, chosen over the whole finished layer.
That choice does not depend on the order, and it keeps today's trace size, which spike 3's union exceeded (9.23 M
searches against 8.42 M). What it would cost: finishing the met layer (+10% in `split-meet`, under load), pair tests
of a met search's layers against the path's terms, and a smallest-key choice. It is cheaper than spike 3 by the second
walk and the wider trace; whether it beats the left-to-right order is unmeasured.

*Pair tests and one canonical path: exact, but slower than the left-to-right order (spike, 2026-10-20, runs
`2026-10-20-pair-exact`, `-pair-cost`; `patches/pair_spike.patch` mode 4, not committed).* Built as surveyed. A failed
search's trace was the walked terms with their subterms, as in mode 3, and a pair test that disagreed with the walk
would have panicked; none did. No order and inner first then mined the same rules in all 15 loops and made the same
9.34 M searches (29% load). Inner first took 345 against 430 us per search (-20%) and 3264 against 3914 s of job CPU
(-17%). Against the committed left-to-right order (`bv_guard`, same gate, 26% load), inner first with this trace ran
349 against 269 us per search (+30%) and 3260 against 2372 s of job CPU (+37%). It also made 9.34 M against 8.42 M
searches, but the search count moves with the rule picks. So every trace no order changes costs more than inner first
saves over the left-to-right order. Finishing the met layer, the pair tests and the wider failed trace together outweigh
the skip. Inner first is decided against (PARKED).

*Related work on canonical paths (surveyed 2026-10-20).*
- Partial-order reduction. The join's canonical orders resemble sleep sets: they cut transitions, not states. Persistent
  sets also cut states, so they would shrink the reached set, and every trace with it. That changes the output, so it
  is not exact by this gate's test.
- Permutation equivalence and standardization (Lévy; van Oostrom and de Vrijer's four equivalences). A standard
  reduction is a canonical representative of the reductions that do the same steps in another order. Standardizing a
  met path would give a canonical path without walking again: reorder its adjacent commuting steps into a fixed normal
  form, which needs pair tests along the path only. It is exact only where the two orders' paths do the same steps in
  another order. Two different derivations of the same length would still differ.
- A trace of redexes instead of terms: each step's rule and the subterm it matched. It is the same under any swap of
  steps at disjoint positions, but not of nested ones, and nested steps are what inner first skips.
- E-graphs (egg) store commuted paths once by construction. Their explanations are proofs found greedily, not
  canonically. This would replace the search's design, not fix its trace.
- No source found combines bidirectional search with a canonical shortest path. The one rule seen is a fixed total
  order on whole paths, not on the meeting vertex.


*How much the join's searches repeat each other (2026-10-20, runs `2026-10-20-class-probe`, `-class-probe-global`;
`patches/class_probe.patch`, `class_probe_global.patch`, counting only, salts 1, 3 and 5 of cold:cmp3d).* Per scoring
thread, each met search's path terms were joined into a class of proven-equal terms (a union-find). Before each search
not served by the memo, the probe checked whether both sides were already in one class. It also counted the reached
terms that an earlier search had reached.
- Within one rule set (classes cleared when the mined rules change): 1.0-1.2% of searches had both sides in one class
  (13.9 k, 12.4 k and 16.0 k of 1.23-1.56 M), and 2.1-2.8% of reached terms were reached before. Sharing work across
  the pairs of one rule set cannot pay: this rules out a union-find or an e-graph per rule set.
- Across rule sets (one set of classes per thread for the whole mine): 61-62% of searches had both sides in one class
  (769 k, 962 k and 858 k), and 96% of those searches met. 71-79% of reached terms were reached before (235 M of 331 M,
  413 M of 524 M, 336 M of 443 M). The memo served 137-217 k searches.
So the join repeats itself across the miner's rule sets, not within one, and the memo captures a small part of that.
The classes ignore which rules a proof used, so 61% is an upper bound on what a cross-rule-set store could serve
exactly. Each class edge is a step by one rule, and an edge holds under a rule set that contains its rule. A store of
proven steps labeled by rule, queried under the current rules, would be sound. It would not reproduce the bounded
search, though: a proof through stored steps can exceed the search's size cap and visit bound, or take another path,
so it changes the output and needs a quality gate, not the exactness gate. Classes are per thread, so the true overlap
across a mine's 6 scoring threads is higher still.

*E-graphs for the join (survey, 2026-10-20).*
- Proofs. egg's explanations (Flatt et al., FMCAD 2022, arXiv 2209.03398) add no asymptotic overhead to congruence
  closure: a greedy O(n log n) pass, smaller proofs than Z3 on 3,760 benchmarks.
- Memory. AC rules are the known cause of e-graph blowup. AC-native matching over multisets (Rosin, Ullrich and Hack,
  EGRAPHS 2026, preliminary) reports asymptotically less memory in some cases.
- Changing rule sets. E-graphs only grow, and no source found retracts what a removed rule derived ("Incremental
  Equality Saturation", EGRAPHS 2025, not read).
The probe above places the sharing across rule sets, and the miner's rule sets add and drop candidate rules. So an
e-graph per rule set shares little (1%), and one across rule sets would need its edges labeled by rule: that is the
store of labeled steps above, with congruence closure on top.

*A store of labeled steps (2026-10-20, run `2026-10-20-store-probe`, `patches/store_probe.patch`, counting only, salts
1, 3 and 5 of cold:cmp3d).* Per scoring thread, for the whole mine, the probe kept each met search's path steps as
edges between terms, each labeled with its law (`lhs`, `rhs`). Before each search the memo did not serve, it looked
for the shortest stored path from one side to the other through edges whose laws are in the current table (within
1000 terms), once at any size and once with every term within the search's cap.
- A path existed for 57-58% of searches (716 k of 1.23 M, 903 k of 1.56 M, 795 k of 1.38 M), against the classes'
  upper bound of 61-62%. Nearly all were within the cap (713 k, 900 k, 793 k), with a mean of 4.9-5.1 steps.
- The search failed on 0.5-0.7% of those (3.9 k, 4.6 k, 5.2 k): there the store would add a joined law.
- Queries took 6-8 s against 322-551 s of searching (summed over threads); the store reached 1.9-2.1 M edges.
So a sound store could serve most of the repetition. The time it would save is not measured: met searches took 203 of
salt 1's 322 s, and the served searches' share of that is unknown.
The probe's store is per thread, and the miner hands candidates to whichever worker is free. A store kept across a
worker's candidates makes a gain depend on which candidates that worker scored before. That is the scheduling
dependence the memo had, removed on 2026-10-18 (`docs/decisions/2026-10-17-monotone-join.md`, "Spike of the
snapshot"). A store that is built only from deterministic searches and is read-only while a round is scored would
avoid it. Terms are interned globally, so workers can share one.

*A shared store fed by the main thread (2026-10-20, run `2026-10-20-store-shared`, `patches/store_shared.patch`, same
salts).* One store per process (a mine), fed only by the miner's main thread: the evaluations of the chosen rules and
the winners' proofs. All threads query it. The workers' searches no longer feed it, so what a worker reads does not
depend on which candidates it scored.
- A path within the cap existed for 77% of searches (950 k of 1.23 M, 1.17 M of 1.56 M, 1.05 M of 1.38 M), more than
  the per-thread store's 58%. Of the workers' searches, 77%, 75% and 76% were served (943 k of 1.22 M, 1.16 M of
  1.55 M, 1.05 M of 1.38 M). The mean path is 4.9-5.1 steps.
- The served searches took 46-55% of the join's search time (137 of 251 s, 201 of 441 s, 194 of 370 s). Queries took
  7-11 s.
- The search failed on 0.7-1.6% of those served (6.4 k, 14.0 k, 16.6 k): there the store would add a joined law.
- The store held only 7.4-7.6 k edges.
So the workers' searches mostly repeat the main thread's evaluation of the chosen rules: each candidate is scored from
an empty memo, and it re-searches the same few thousand pairs. A store of a few thousand steps would serve three
quarters of the searches and save about half the join's search time, less the queries.
The probe let the main thread write while the store was in use. In the miner it writes during a round when it proves a
winner between chunks, and the chunks depend on the thread count (`threads * 4` candidates each). A kept store must be
frozen per round, a snapshot taken when the round starts, so the gains do not depend on the thread count.

*Spike of the join store (2026-10-21, runs `2026-10-21-store-gate`, `-store-threads`; `patches/store_spike.patch` on
0e1dab3's code).* One store per mine (`JoinStore`), emptied when the miner starts and fed by its main thread's met
searches. Each step is kept with its subterm's path and its law's key (`lhs`, `rhs`, direction), so a table finds the
step under that key whatever its index, and plans are rebuilt by `step_plan` under the caller's counting mode. Before
it searches, `join_eq` (with the memo on) looks for the shortest stored path through the current table's laws and
terms within the cap (1000 terms at most); if it finds one, the plan is the path's steps, and the trace is the path's
terms with their subterms, as for a met search. The main thread reads the store itself; the other threads read a copy
frozen when each round of scoring starts.
- Gate against `bv_guard` (salts 1-5, the arms run side by side, the machine loaded by other sessions at 64-72%): M 363
  against 362, rules at the end 993 against 918, joined laws 825 against 753, exhausted 0 in both. Rules differ in
  every loop, as a store that is not exact must make them.
- Cost: job CPU 2534 against 1439 s (-43%), wall 536 against 306 s. The join ran 1.95 M searches against 8.42 M
  (3575 against 1514 s searching); the store served 6.23 M joins in 78 s of queries.
- Thread check (salt 1): rules at 6 and 1 threads byte-equal in all 3 loops.
So the store keeps M (one lower) with a smaller library, takes 43% off the job's CPU, and keeps the miner independent of
the thread count.

*The join store, built (2026-10-21, runs `2026-10-21-storekept-gate`, `-storekept-threads-s1`, `-s5`).* Built
test-first (`join_store_serves_a_stored_path_under_its_laws_only`, `join_store_workers_read_the_frozen_copy`). Kept
code has no globals, unlike the spike, whose process-wide store would have been shared by parallel tests and by any later
joins in the process. Each thread has its own `JoinStoreUse`. The miner's main thread holds the `Feed` it fills, from
the miner's start to its end. Each round's workers get a `Read` of the copy `frozen_join_store` takes as the round
starts. A thread without one is never served. The table's steps are found by law through `RuleTable::join_key`, built
with the table, so no fingerprint cache is needed. Gate against `bv_guard`: M 363 against 362, job CPU 2321 against
1297 s (-44%), wall 320 against 194 s. Its rules are byte-equal to the spike's in all 15 loops, and byte-equal at 6
and 1 threads on salts 1 and 5. A review (2026-10-21) found what those checks missed. `join_search` feeds the store
from every met search, while reads require the memo to be on. The miner's proofs run on the main thread only at 1
thread (`prove`) or when not speculated (`prove_any`), so the store's contents, and through them a candidate's gain,
can depend on the thread count. Fixed in fbfda55: a search feeds the store only under the condition that reads it (the
memo on, no rule blocked), test `join_store_is_fed_only_where_it_is_read`. Gate against `bv_storekept` (runs
`2026-10-21-storefix-gate`, `-storefix-threads-s1`, `-s3`, `-s5`): M 362 both, rules byte-equal in all 15 loops, job CPU
1230 against 1240 s; rules byte-equal at 6 and 1 threads on salts 1, 3 and 5. So at 6 threads the proofs' paths changed
no rule. The same commit tests a path read backwards, through several steps and after its law moves in the table. The
review's note that the store's query overshoots `JOIN_VISIT` within a layer stands as designed: the search is bounded
once a layer too.

*Whether the memo's join entries can go (2026-10-21, a reading of the code).* No, not as a deletion. The memo's join
entries (`RewriteMemo::joins`) do three things the store does not.
1. They keep failed searches. The store keeps only met paths, and failed searches are the costly ones (119 of salt 1's
   322 s of searching in the store probe).
2. They serve a worker's repeats within one candidate. The worker's store is a read-only copy, so a pair the worker
   searched itself is not in it.
3. On the main thread, `state` seeds each round's memo with the previous round's entries, filtered by trace.
Removing them would need a negative store and a per-candidate overlay on the workers' copies: that is a second cache
in another shape, not one fewer. What could merge is the met entries alone, if most memo hits are on met pairs the
store already serves (parked; counted in the next paragraph).

*Memo join hits by kind (2026-10-21, run `2026-10-21-hit-probe`, `2026-10-20/patches/hit_probe.patch` on e8bac31,
`2026-10-20/scripts/hit_probe.sh`, cold:cmp3d salts 1, 3, 5, counting only).* Each memo join hit was counted by met or
failed, by the miner's main thread or a worker, and by whether the thread's store would serve the pair. Over the three
salts, 552271 of 572099 hits (96.5%) were met and 19827 failed. The main thread's 141612 met hits were all served, as
expected, since it feeds the store from its own met searches. The workers' 410659 met hits were 88.3% served (362542).
The other 48117 are the workers' repeats, within one candidate, of pairs searched after the freeze. The store would
serve 88.1% of all hits (87.1%, 87.1% and 90.5% per salt) and none of the failed ones. So the parked trigger is met by
count. But merging the met entries into the store removes no concept. The memo stays for the failed pairs and for the
workers' unserved repeats, which would otherwise be searched again (about 0.35 ms each, about 5-8 s of search per salt).
A store query costs about 5 us (6 s over 1.16M queries in salt 1), against a hash lookup for a hit. A served path can
also differ from the memo's plan, since it is the shortest stored path, not the one the search met on. Traces and gains
could then change. The counts predate the fix for the thread-count finding above. The runs used 6 threads, so proofs fed
the store only through `prove_any` run inline.

*The order within a round of `quiet_ab.sh` (2026-10-19, rows of this day's A/Bs).* The second arm of a round was slower
by +6.5 s and +6.7 s (7 of 8 rounds) in `-fits-quiet` and `-pairs-quiet`, +10.0 s in `-room-quiet`, but -1.7 to +2.4 s
in `-spine-main-quiet`, `-spine-back-quiet` and `-shape-quiet`. The script alternates the order, so the medians stay
fair, but the won count can read a 3% gain as 5/8. Read an A/B by the mean over the two orders (each arm first in half
the rounds); the verdicts of this day's earlier A/Bs stand that way too (room +3.6 s, fits +0.3 s, shape -22.3 s). `runs time` now prints that mean, and the cost of running second, under each won count.

*How much the size bound would skip (2026-10-18, run `2026-10-18-size-bound`, `patches/size_bound.patch`, counting
only).* The bound on a step's rewritten subterm, `max(size(to), size(t) + size(to) - size(from))` (the second only when
every variable occurs in `to` at least as often as in `from`), is a lower bound on the step's size, so skipping a rule
when it exceeds the cap changes no search: in salt 1's cold:cmp3d loops it never skipped a match within the cap. It would
skip 43% of the matcher's 5.84G calls before matching, and 96% of the 1.36G matches over the cap with them (so their
`subst_sig` too). With `match_pat` from the walk at 13.9% and `subst_sig` at 12.2% of the lazy join's profile, that is
on the order of a tenth of the join's CPU, unmeasured. (The calls differ from `-match-count`'s 5.54G by the timing
one-off.)

*Lock-free interner reads (2026-10-18, run `2026-10-18-interner-ab`).* `Term::op`'s shared table is now per shard an
open-addressed array of node pointers read without a lock (cells go only from null to a node; a full array is replaced by
a doubled copy, the old one leaked), and only a new node takes the shard's mutex. Test
`op_racing_threads_make_one_node_per_term` (eight threads making the same 100000+ new terms, the table growing under them)
guards the one node per term. Salt 1 cold:cmp3d at 1 lane, run in the order old, new, new, old (CPU 21% at start, RTP
off): 136 and 140 s against 150 and 142, about 5% less wall, against the profile's 8.5% for the mutex. Rules and M
(29/17/30) agree in every run but the first old one, which differs in loop 15-2 only: the timing one-off above, not the
table.

*Profile after the lock-free reads and the memo per candidate (2026-10-18, run `2026-10-18-pcand-prof`).* Same script as
`-lazy-prof` (8528735 with debug info; CPU 28% at start, RTP off; frames in
`docs/runs/2026-10-18/rows/2026-10-18-pcand-prof.txt`). Of 407479 busy samples:
- `join_search` 85.3% inclusive; `Trace::touched_by` 3.3%, `rewrite` 5.2%;
- `Term::op` 22.2% inclusive and no mutex: `Cells::find` 10.9% (node compares 5.9%, loading cells 4.3%) and the thread's
  cache slot check 8.6% (`filter` 4.2%, node compare 4.4%), so its cost is now loads of cold nodes and cells, on misses as
  well as hits; most calls come from `place` (17.2% inclusive);
- `match_pat` 21.1% inclusive (19.8% self; 16.5% from `join_walk`, 2.7% from `touched_by`);
- `subst_sig` 14.0% inclusive (6.6% self, its `sh_op` hashing 4.4%).
Levers, by estimated share (none measured): the size bound before matching (parked; it skips 43% of the walk's matcher
calls and 96% of over-cap matches with their `subst_sig`, roughly 10-15% of samples); building a step's term only when it
is expanded (up to 63% of `place`, about 11%, but `seen` must then compare unbuilt steps); hash tags beside the interner's
cell and cache pointers so a mismatch needs no node load (part of the 10.3% of node compares); a cheaper `sh_op` (one
finaliser, not two; about 2%).

*The size bound and the interner's tags, built (2026-10-18, run `2026-10-18-sbound-tag-ab`, script
`scripts/arms_ab.sh`).* `JoinEq::min_size` (8de04c1; test `join_min_size_is_a_lower_bound`) skips a rule unmatched in
`join_walk` when its bound is over the cap; the interner's cache slots and cells hold node addresses tagged with 16 bits
of the hash (2de4854), so a lookup passes over other nodes without loading them. Salt 1 cold:cmp3d at 1 lane, in the
order base, bound, both, both, bound, base (CPU 30% at start and 79% when sampled mid-run: other sessions, so contended;
RTP off): every sweep gives the same files; wall 198, 200 and 198 s per arm (two sweeps each), so no change; the
miners' summed join seconds 699, 670 and 639 s, so 4% less with the bound and 9% with both, against the profile's
estimate of 10-15% for the bound alone. That contention hid the gain: on a quieter machine (run
`2026-10-18-sbound-tag-quiet`, `runs time` through `scripts/quiet_ab.sh`, arms alternated, 2 rounds each, others' load
16-23%, so no round was clean by its 20% limit) the same arms took wall 86.4/89.6, 78.9/77.7 and 78.7/76.8 s and job
CPU 366/379, 326/322 and 325/317 s, all files the same: the bound cuts 11% of wall and 13% of CPU, the tags about 1%
more.

*Where the sweep's wall goes (2026-10-18, profile `2026-10-18-pcand-prof`, `scripts/prof_timeline.py`).* Counting the
threads busy in each millisecond of the 97 s profiled sweep (a sample is busy when its CPU delta is at least half the
interval): 4.1% of the wall has no thread busy, 26.8% one, 6.8% two, 5.5% three, 6.6% four, 11.7% five, 35.7% six and
2.8% more. In the one-thread stretches the miner's main thread does 20.5 s of work and a lone scoring worker 5.2 s (a
round's last candidate). The main thread (25.3 s in all, `PROF_THREAD=search::rule_miner prof_named.py`) spends 53% in
`Trace::touched_by`, nearly all of it computing each round's `affected` (every candidate against every law's trace,
in `pick`) and 38% in `rewrite_plan` under `score_laws` on the main thread (the chosen set's evaluation, `state`, with
its seeded memo, among them; not split further). Both run while the scoring workers wait. Levers: compute `affected` on the scoring workers (independent per candidate, so the same result; about 13 s
of serial work, so up to about 11 s of this sweep's wall); make `touched_by` cheaper (an index from rule to trace terms,
the same result); and evaluating the chosen set in parallel, which would split its seeded memo, and the memo's join
entries are inexact (the timing one-off above), so it could change results: not exact as it stands.
The first two are built (run `2026-10-18-aff-index-ab`, `scripts/salts_ab.sh`, 2de4854's exe against this one, salts
1-4, others' load 29-51%, RTP off): `TraceIndex` (test `trace_index_agrees_with_touched_by`) holds every law's trace
items once each, with the laws they are in, grouped by shape, so a candidate matches a term shared by many laws' traces
once; and the candidates' `affected` is computed on the scoring threads. Rules byte-equal and M equal in all 12 loops
(293 in both); the miners' time bounding the gains, summed over the 24 mines, 138.2 against 13.5 s; wall 490 against
434 s (-11%) and job CPU 2909 against 2847 s, both under that load. The chosen set's evaluation stays serial (parked).
Re-profiled at 3a851d6 (profile `2026-10-18-aff-prof`, same sweep, CPU 36% at start against 28%, so not comparable in
wall: 102.7 s against 97): the main thread has 13.6 k busy samples against 25.3 k, and it is alone for 8.9 s against
20.5 s (one-busy wall 20.2% against 26.8%). Of what is left on it (`PROF_PARENTS` in `prof_named.py`, which names what a
numbered closure calls): 52% is `score_rule` in `pick` (it only calls `score_laws`), which on the main thread runs only for
the winner's rivals, scored one after another; 25% is `state` (the chosen set's evaluation); 12% is the winner loop's own
code; `TraceIndex::new` is 3%. The winner loop's share is not its `best` scan: its samples end in the kernel under
`WaitOnAddress` / `NtWaitForAlertByThreadId` (the thread parking on the workers' results, much of it under the profiler's
`RtlWalkFrameChain`), with thread creation 0.2%, so keeping the best gain incrementally would save nothing (not built).
Scoring the rivals on the scoring workers is exact: each is scored from an empty memo and the choice among them runs
afterwards in the same order. Built: the winner's rivals go through the round's worker queue (run
`2026-10-18-rivals-pool-ab`, `bv_aff` against this, salts 1-4, others' load 48-58%, RTP off): rules byte-equal and M
equal in all 12 loops (293); wall 513 against 475 s (-7%), job CPU 3094 against 2974 s, both under that load. At 1
and 6 scoring threads the rules stay the same (run `2026-10-18-rivals-threads`, `threads_check.sh`, salt 5).
On a quiet machine, the two main-thread moves together (`bv_riv` against `bv_both`, the commit before them; run
`2026-10-18-miner-serial-quiet`, `quiet_ab.sh`, salt 1 at one lane, RTP off) gave the same files, wall 73.6 against 58.2 s
(-21%) and job CPU 301 against 291 s (-4%): work moved off the waiting main thread, not work saved. That is one clean round:
the machine was quiet for only one of the rounds the 3 h deadline allowed (the other's load 18-28% gave 66.6 s).
`state` in parallel would also be exact (surveyed, not built): its seed is reusable only because every memo entry is a pure
function of its key, so each worker can take the whole filtered seed, evaluate a share of the laws and hand back its grown
memo for a union merge. It needs the memo's `Rc`s made `Arc` (or copied per worker) for about 3.4 s of a ~100 s sweep
(PARKED.md, "The miner's serial main thread").

*Where the streams sweep's time goes (2026-10-26, profiles `2026-10-26-cu14-base-prof` and `2026-10-26-cu14-d3-prof`,
`docs/runs/2026-10-26/scripts/streams_prof.sh`, frames named by `prof_named.py`).* The first whole-sweep profiles since
2026-10-23, both of c7377b9 with debug info, salt 1. At the base: building the 2-growth law sequence
(`stream_sequence`) is 31.8% inclusive, and nearly all of that is its `stream_laws` filter's `verdict` (26.8%);
`prove_eq` is 53.9% (its join, `join_eq`, 36.0%; the per-position step `eq_pos` 17.5%); the kernel's checks 4.4%;
`interp` alone is 25.7% self time. At 4950 large extras (the deep-extras patch of "At every size, and at three times
the count", 11 min) the join search dominates: `score_laws` 84.5% inclusive, `join_search` 67.2% (`join_walk` 60.0%),
with `stream_sequence` 11.9%, `verdict` 9.7% and `eq_pos` 8.6%. Both `verdict` and `eq_pos` spent their time in one loop:
every input tuple at widths 1-5, two recursive `interp`s and an allocation per tuple.

*One exhaustive check for both (2026-10-26, 14a21d4).* `bitwise_holds` (`crates/church-bv/src/rewrite.rs`) replaces that
loop in both places: per width it builds every input once (`ValueMemo::exhaustive`, one byte per value) and compares
the two terms' whole value vectors (`first_difference`); a test pins it to the per-tuple answer on every add-free pair
of the generator's terms (`bitwise_holds_is_the_per_tuple_check`). Gate `2026-10-26-cu15-ab` against R (salts 1-3,
untimed, JOBS=3): rules the same in 9 of 9 loops, M 477, held-out 6400 and every band equal; work counts walk equal,
match +19 k of 4.77 G, op +115, and `interp` 75.8 G to 0 (all of it was these checks); job CPU 978 to 553 s
(338 to 218, 346 to 203, 293 to 132 per salt). The base profile's `verdict` share was nearly all this loop, so the
next lever on the sequence (cleanup plan CU17, building only the prefix that is read) was re-measured: the base salt
re-profiled at 32fb207 (profile `2026-10-27-cu17-base-prof`, untimed) took 52.6 s against 154.9 s with 219 k busy samples
against 343 k, and the sequence 23.3 s against 109.5 s (its `STREAMS` line). The sequence is now 10.6% of samples:
grouping the grown terms by width-4 values (`pool_conjectures`) 5.8%, most of it `ValueMemo::values`, and the filter a
prefix would shorten (normal forms and width-8 values) only 2.6%. It is still built on one thread before anything else
runs, so it is 23 of the 53 s of wall. The join search is 62.0%.

*The streams in parallel (2026-10-27, cleanup plan CU18).* `stream_sequence` now builds the 56 streams on
`STREAM_THREADS` scoped threads (default 4), each taking the next stream when free, and merges them by stream index, so
the sequence is the same at any thread count (`a_stream_sequence_is_the_same_on_any_thread_count`). Built alone (probes
`2026-10-27-cu18-seqmem` and `-b`, salt 1, 58125 laws each): 1 thread 15.4 s and 1410 MB peak commit, 2 threads 8.7 s
and 2050 MB, 4 threads 5.4 s and 2818 MB, 6 threads 4.3 s and 3074 MB, 12 threads 3.7 s and 4610 MB, with job CPU 15.3
to 32.2 s. The peak grows with the thread count (each thread holds one stream's grown terms at a time, an inference,
not profiled); 4 is the default
because three gate processes then fill the 12-thread cap and most of the speedup is in. Gate `2026-10-27-cu18-ab`
against 74c575b (salts 1-3, untimed, JOBS=3): rules the same in 9 of 9 loops, M 477, held-out 6400 and every band equal;
work walk equal, match +10 k of 4.77 G, op -115. Timed (`2026-10-27-cu18-timed-2`, salt 1, quiet machine): the
sequence 16.1 to 5.4 s and the sweep's wall 35.5 to 24.6 s (-31%), job CPU 144.9 to 146.6 s; the arm's peak commit
rises from 1538 to 3074 MB and is still the sequence's.

*Grouping the streams' terms, and the 2-growth build inside the 4-growth one (2026-10-28, probe
`2026-10-28-stream-probe`).* A copy of `stream_laws` with timers (`docs/runs/2026-10-28/patches/stream_probe.patch`,
one thread, salt 1; its laws asserted equal to `stream_laws`' for all 56 streams at 2 and 4 growths, in two runs)
splits a build (the totals, the five largest pools and the figures below, derived by
`docs/runs/2026-10-28/scripts/stream_probe_derive.py`, are in `docs/runs/2026-10-28/rows/2026-10-28-stream-probe.txt`).
At 4 growths the 56 streams put 4.32 M terms into `pool_conjectures`, whose memo fills 8.11 M vectors (the terms and
their subterms); they fall into 2.48 M groups, and 51.9% of the terms are in groups of two or more (52.2% at 2
growths). That gives 1.84 M conjectures, 1.14 M after the grown-side and three-variable filter, 247 k open, 12.6 k
refuted at width 8, and 234 k laws. Time, on one thread on a machine loaded by other sessions (55-83% in spot samples;
shares only, two runs),
at 4 growths: `pool_conjectures` 52-53% of the build (filling vectors 30-31 points, copying each vector into its key
and pushing the comparison byte 11-13, the map insert 7, sorting the conjectures 3), the open-law filter 33-35%
(`Classes::normalize` 28), and growth, sorting and setup 13-14%; at 2 growths `pool_conjectures` is 52-58% and the key
copy 8-15 points. That is close to the 4-growth build's profile in "A join budget for the mines alone" (grouping 52%,
fill 31 points, the key copy 9 as realloc and dealloc, the filter 33, the rest 15). Normalize is cheaper the second
time: 14 of the streams (every fourth) took 4.9-5.4 s of it in the probe's two runs, but 1.4 s when each was built
again right after a first build of the same stream in the same process (`stream_probe_overhead`: the 14 first builds
took 19.4 s, the second ones 15.1 s). Those two figures come from different processes; within one process the gap is
mostly first-ask misses in the process-wide memos `Classes::normalize` reads (`VERDICTS`, the class lookups), measured
below in "Why normalize is slow on a cold stream". Three levers, the first two measured, the third a structural check:

- *A prefilter.* Group first on 16 fixed inputs and fill full vectors only for terms that share a bucket. It is exact
  (the same conjectures, asserted), since equal vectors agree on any subset of inputs. But with 52% of the terms in true
  groups it can skip at most about 48% of the terms and 50% of the fills; 16 inputs come within 2.9 points of that
  floor on terms and 3.2 on fills (64 inputs within 0.2). At 4 growths the fill, key and insert time fell from 44.9 to
  21.6 s (run 2: 39.9 to 20.2). Per stream, over the 55 whose single stage takes 0.05 s or more, the ratio's median is
  0.44-0.45 and the prefilter is slower on 11 (at 2 growths: 0.56-0.57, slower on 7-10 of 50-52). 19 streams keep over
  90% of their terms even at 16 inputs (add,sub: all 73,671 of its 74,396 terms that are in groups of two or more, 2,530
  groups).
- *Vectors shared across streams.* 12.6% of the 8.11 M fills at 4 growths repeat another stream's (19.8% at 2), and a
  process-wide memo of the 7.09 M distinct terms would take 29 GB at 4096 bytes each. Decided against: the memory buys
  at most an eighth of the fills (`PARKED.md`, "One value memo shared by the streams").
- *The 2-growth build is the 4-growth build restricted.* For every one of the 56 streams the 2-growth pool, in
  `pool_conjectures`' order, is a prefix of the 4-growth pool, and the 2-growth laws are, in order, the 4-growth laws
  with both sides in that prefix (test `stream_probe_nested`; on 2 streams, and,or and shl1,shr1, both lists are empty).
  By construction: levels 1 and 2 draw the same terms at the same salt, the pool is sorted by (level, `show`), so a
  group's first member is the same; the comparison flag is in the group key, the grown-side and three-variable filter
  and the open-law checks are per law, and conjectures are sorted by their text and `shuffled` orders laws by a hash of
  the salt and each law's own text, so restricting keeps the order. The merge of the streams (`build_sequence`) does not
  commute with restricting, so the 2-growth sequence is not the merged 4-growth one filtered (below, "Deriving the
  2-growth sequence from the 4-growth build"). A sweep builds both sequences at one salt unless `GEN_DRAW` is set
  (`window` and `scope_extras` in `crates/church-bv/src/driver.rs`).

Chosen 2026-10-28: exact value-class ids in `ValueMemo` (`ValueMemo::class`, one id per distinct vector; commit
`cd7dacb`). The three map keys that copied a 4096-byte vector (`pool_conjectures`, `miner::Pool`'s two indexes) key on
class ids, the grow filter compares class ids, and the width-8 open-law check compares in place (`ValueMemo::agree`).
Both sequences stay byte-identical (test `stream_sequences_are_pinned`: 58,125 and 230,801 laws at salt 1). Counted
on that test (3 runs each on CPU 4, runs `2026-10-28-class-ids-icount-A2` and `-B2`): 490.43 G instructions before,
466.59 G after (best; -4.9%; medians -4.8%; (median - best) / best 0.0003 and 0.001, one run before at 1.010 of
its best). A profile of that test after the change (run `2026-10-28-class-ids-prof`, 83,040 busy samples; frames in
`docs/runs/2026-10-28/rows/2026-10-28-class-ids-prof.txt`): `pool_conjectures` 44.0%, of it filling vectors (`zip_op`) 28.6 points and the class lookups 1.5;
the open-law filter (`scoped`) 36.1%, `verdict` 16.1, `ValueMemo::agree` 9.8; `memset` 3.0% (2.0 points directly under
`pool_conjectures`, where the fill and its zero-fill are inlined, 0.9 under `agree`). `zip_word` evaluates each byte through `u128` (`Word::get` and `of`; `of`
alone is 12.4% self), and the `u8` loop is not vectorized as byte arithmetic: its hottest block (the `sub` loop, RVA
0x2f200 in the profiled exe) loads, subtracts and masks one byte at a time in 32- and 64-bit registers and packs the 16
results into an xmm register for the store. The prefilter's trigger, filling at about a third of a build, was about met here (`PARKED.md`, "A
prefilter before the full value vectors"); with `zip_word` on native bytes (below, landed) filling is about a tenth.

*Without the fill's zero-fill (2026-10-28, patch `docs/runs/2026-10-28/patches/zero_fill.patch`): within the noise.*
`fill` resized the last block with zeros and then overwrote them; the patch has `zip_op` write into the block's spare
capacity (`MaybeUninit`, then `set_len`), three new `unsafe` blocks (two in `fill`, one cast of initialized bytes in
the classes' `zip` closure). Both sequences stay pinned. Counted as above (runs
`2026-10-28-zero-fill-icount-C` and `-B`): 460.87 G instructions against 463.66 G for the build before it in the same
session (best of 3; -0.6%, medians -0.7%), while that build itself counted 466.59 G an hour earlier, so the two
sessions' counts of one exe differ by 0.6% (the 4 build threads share memos behind locks). Not kept then: at most
0.7% of the work, and it would be the repo's first `unsafe` over uninitialized memory. Recounted on typed rows and
landed below ("The zero-fill patch on typed rows", "Landed with both checks").

*`zip_word` on native bytes (spike, 2026-10-28, patch `docs/runs/2026-10-28/patches/zip_word_native.patch` on
08ff13a; landed 2026-10-29 with typed rows, below): 38.8% fewer instructions.* Of the eight `u8` loops, only `add`, `sub` and `shl1` did scalar
arithmetic. The operators were defined on `u128` only (`OpInfo::word`), and the backend did not narrow a 128-bit add,
subtract or shift to byte lanes: these loops load 16 bytes, spill them to the stack, work one byte at a time in 32- and
64-bit registers (`sub`: 10 `subl`, 6 `subq`) and pack the results back, 131 instructions per 16 bytes in `sub`, about
8 a byte. `and`, `or`, `xor` (`andps` and the like), `lt` (`pmaxub`, `pcmpeqb`) and `shr1` (`psrlw`) were already
vector loops. The patch states each operator once, generic over `Word` (`rewrite::word<W>`, used by `zip_word` for
both word types and by `Term::interp`), so the `u8` loops do byte arithmetic: `psubb` or `paddb` and `pand`, 13
instructions per 32 bytes for `add` and `sub`, 11 for `shl1` (`paddb x, x`); the other five loops are instruction for
instruction unchanged (`docs/runs/2026-10-28/rows/2026-10-28-zipword-disasm.txt`, by
`docs/runs/2026-10-28/scripts/zw_dis.sh`). Both sequences stay byte-identical (run `2026-10-28-zipword-pin-D`).
Counted as above, the two exes built in one session (runs `2026-10-28-zipword-icount-M` and `-D2`; `cargo test
--release`, the `sweep` profile's fat LTO not checked): 466.14 G instructions before, 285.22 G after (best of 3;
-38.8%, medians -38.6%; (median - best) / best 0.005 and 0.008, one run after at 1.016 of its best). If the saving
is all in those three loops (the other five and the inlined `u128` fill are the same size before and after;
`Term::interp`'s code was not compared), they were at least 38.8% of the instructions, against 33.0% of the busy
samples (`zip_op` inclusive, run `2026-10-28-class-ids-prof`). A profile after the patch (run `2026-10-28-zipword-prof`, a line-tables-only build
of the same source; frames in `docs/runs/2026-10-28/rows/2026-10-28-zipword-prof.txt`): `zip_op` 10.5%, 8.5 points of
it under `pool_conjectures` (28.6 before); `pool_conjectures` 30.2%; the open-law filter (`scoped`) 43.3%, `verdict`
19.0, `ValueMemo::agree` 7.8; `memset` 4.2% self (2.8 points directly under `pool_conjectures`, 2.0 before). The two
profiles ran at 43% and 3% machine load, so only shares within each compare (busy samples 83,040 and 50,152). Not
timed. With the patch, filling is about a tenth of the build, below the prefilter's trigger (`PARKED.md`, "A prefilter
before the full value vectors").

*Landed with typed rows (2026-10-29, commits `a63ff57`, `7637e88`).* The patch's `word` was a `match` on the operator
ending in `unreachable!`, so an operator without an arm failed at run time where a row without its `OpInfo::word`
closure had failed to compile; a table row cannot hold one function generic over `Word`. Instead each `OP_INFO` row
carries `Words { w8, w128 }`, built by `words!(|x, y, m| body)` from one body typed as a `u8` and a `u128` function:
`zip_word<W, O>` takes the row's function for `W` (`Word::pick`) as a constant, so it inlines as the `match` did, and
`Term::interp` calls the `u128` one through the pointer. `OP_INFO` stays the one place that says what an operator
computes, and a row without its body fails to compile (E0061, checked by deleting one). A const assert keeps
`OP_INFO` within the 8 bits the class shape gives the root operator (E0080, checked by tightening it to fewer than 8
with the eight rows; a real ninth row first fails on `OP_INFO`'s declared length and the other eight-entry arrays). Because one body
now makes both functions, the byte and `u128` loops agree by construction, so the new test
`operators_match_a_bit_at_a_time` checks every operator through `zip_op` on both word types against a version worked
out a bit at a time (a ripple carry for `add`, `sub` and `lt`): all pairs of inputs at widths 1 to 8, sampled ones at
16, 64, 127 and 128 on `u128`, and once from index 1 so the scalar tail runs. With `sub`'s operands swapped it fails
(`sub 1 0 at width 2 in u8`: 3, not 1) while `value_memo_matches_interp`, which compares the memo with
`Term::interp`, passes. Checks (runs `2026-10-29-typedrows-*`): the full `church_bv` suite passes (161); both
sequences stay pinned; the eight `u8` loops are instruction for instruction the spike's
(`docs/runs/2026-10-29/rows/2026-10-29-typedrows-disasm.txt`); the pin test counts the same, typed rows against the
spike's exe in one session (best 289.78 G against 289.96 G, medians 292.27 and 292.29 G, spreads 0.8-0.9%;
`docs/runs/2026-10-29/rows/2026-10-29-typedrows-icount.txt`). The spike's exe counted 285.22 G the day before, 1.6%
lower: only counts from one session compare. As for the spike, not timed, and the `sweep` profile (fat LTO) not built. A profile after landing (run `2026-10-29-typedrows-prof`, 61,620 busy
samples at 13% machine load; frames in `docs/runs/2026-10-29/rows/2026-10-29-typedrows-prof.txt`) has the spike's
shares within about three points: the open-law filter (`scoped`) 46.5%, `pool_conjectures` 27.7, `verdict` 18.9,
`Term::show` 10.8, `zip_op` 9.7 (7.5 points under `pool_conjectures`), `ValueMemo::agree` 8.2; the rows' closures appear
only inlined under `zip_word`. `Plan::new` doubled (6.4% against 3.2), most of the rise in its allocations: mimalloc's
`mi_arena_try_purge` is 3.8% self, 2.6 points of it under `Plan::new`'s (0.5% in run `2026-10-28-class-ids-prof`,
under 0.6% in run `2026-10-28-zipword-prof`). The loops are the same, so this reads as the allocator returning memory
on a timer, not as a change in the code; not counted here (the "P1 spike" below counts purging).

*The zero-fill patch on typed rows (2026-10-29, patch `docs/runs/2026-10-29/patches/zero_fill_on_7637e88.patch`):
-1.4% with the streams built on one thread.* The patch above ("Without the fill's zero-fill") rebased onto `7637e88`.
It keeps that patch's three `unsafe` blocks (the fill's two and a cast of initialized bytes in the classes' `zip`
closure) and adds the same cast where the new test `operators_match_a_bit_at_a_time` calls `zip_op`; only the fill's
two touch uninitialized memory. The full `church_bv` suite passes (161), both sequences stay pinned (runs
`2026-10-29-zerofill2-suite`, `-pin`), and the eight `u8` loops are instruction for instruction the same with and
without it, as in the typed rows and the spike (addresses masked; `docs/runs/2026-10-29/scripts/zw_diff.sh`,
`docs/runs/2026-10-29/rows/2026-10-29-zerofill2-disasm.txt`). Counted as above (the pin test, 3 runs per round on
CPU 4) with `STREAM_THREADS=1` (default 4, "The streams in parallel"), set in `B.exe.env` and `C.exe.env` because
the elevated count task runs the exe in its own environment (`Setup::process`, `crates/church-bv/src/job.rs`); a direct
run of the unpatched exe printed `ENV STREAM_THREADS=1` and "on 1 threads". Two rounds, unpatched then patched and
then the reverse (runs `2026-10-29-zerofill2-icount-*`, `docs/runs/2026-10-29/rows/2026-10-29-zerofill2-icount.txt`):
298.10 G instructions with the patch against 302.46 G without (best of 6; -1.44%, medians -1.40%). The arms' ranges
are 1.9 G apart, and each round of 3 spreads 0.16-0.29%. At the default four threads, one round each in the same
session: 288.98 G against 291.96 G (best of 3; -1.0%, medians -2.0%). Four-thread rounds spread 0.2-1.1%, though
(this unpatched one 1.1%), and that unpatched round counted 0.75% above the same code's 289.78 G earlier the same day
(typed rows, above), so four threads confirm only the direction. The profile after typed rows has `memset` at 4.1%
self, 2.8 points directly under `pool_conjectures` (run `2026-10-29-typedrows-prof`). Not timed. Landing it needs
two checks first. `ValueMemo::new` does not check that each variable's vector is `len` long, and `fill` copies those
vectors into the block (`extend_from_slice`), so a wrong length would misalign the block, and the patch's write of
`len` cells could then run past the block's capacity: an out-of-bounds write from safe code, where `resize` grew the
vector instead. All five callers pass `len`-long vectors, and an `assert!` in `new` would close it. Also, `zip_op`
writes only as many cells as its shortest slice, so the fill's `set_len` is sound only because the children's slices
are `len` long too (they are cut `[..len]`); a `debug_assert!` on equal lengths in `zip_op` would state that.

*Landed with both checks (2026-10-29, commit `c8c2e68`): no more work than the patch.* `fill` writes into the block's
spare capacity through `fill_op`, which takes `MaybeUninit` cells and picks the operator's `zip_word` once per call;
`zip_op` keeps its signature for initialized outputs and casts once to call `fill_op`, so the classes' `zip` closure
and `operators_match_a_bit_at_a_time` need none of the patch's casts. That leaves three `unsafe` blocks: the fill's
two (the block split into its written cells and the next `len` uninitialized ones, then `set_len`) and `zip_op`'s
cast; only the fill's touch uninitialized memory. Both checks are `assert!`s, not `debug_assert!`s, since the counts
and the streams run release builds: `ValueMemo::new` refuses a variable vector of another length, and `fill_op`
refuses inputs whose length is not its output's (only then does it write every cell). Each has a `should_panic` test,
watched failing first (`value_memo_refuses_a_variable_of_another_length`, `zip_op_refuses_a_shorter_input`). The suite
passes (163) and both sequences stay pinned (runs `2026-10-29-zerofill3-suite`, `-pin`). Counted against the patch's
exe in one session with `STREAM_THREADS=1`, rounds landed, patch, patch, landed (runs `2026-10-29-zerofill3-icount-*`,
`docs/runs/2026-10-29/rows/2026-10-29-zerofill3-icount.txt`): 298.36 G instructions against 300.27 G (best of 6;
-0.6%, medians -0.4%), inside both arms' spreads (pooled (median - best) / best 0.5-0.75%), so the checks and the
restructuring cost nothing measurable. The patch's exe counted 0.7% (best) and 0.9% (median) above its own counts a
few hours earlier (`2026-10-29-zerofill2-icount`), so one stream thread does not remove the drift between batches of
counts; mimalloc's purging adds spread to counts ("P1 spike" below), but how the drift splits between purging and load
is still open. A profile after landing (run `2026-10-29-zerofill3-prof`, 56,466 busy samples at 8% machine load;
frames in `docs/runs/2026-10-29/rows/2026-10-29-zerofill3-prof.txt`): `memset` 0.18% (4.1% self after typed rows);
the open-law filter (`scoped`) 45.4%, `pool_conjectures` 28.4, `verdict` 18.7, `fill_op` 11.7 (8.8 points under
`pool_conjectures`), `Term::show` 11.0, `ValueMemo::agree` 7.9; `mi_arena_try_purge` 3.8% self, 2.6 points of it
under `Plan::new`'s allocations, as after typed rows.

*Why normalize is slow on a cold stream (2026-10-28, runs `2026-10-28-normalize-cold`, `-twice`, `-twice-all56`,
`-twice-nolp`, `-once-all56`, `-origins`, `-distinct`).* The 4.9-5.4 s against 1.4 s above compared the probe's
56-stream processes with `stream_probe_overhead`'s 14-stream one, on a loaded machine. A probe that counts
`Classes::normalize`'s work (`docs/runs/2026-10-28/patches/normalize_cold_probe.patch`, on 3662451 with the stream probe,
before `cd7dacb`; one thread, salt 1, pinned to CFF at BelowNormal, load 16-49%, no CPU lease; figures from
`docs/runs/2026-10-28/scripts/normalize_cold/`, collected in `docs/runs/2026-10-28/rows/2026-10-28-normalize-cold.txt`)
builds each of the 14 streams at 4 growths twice in a row. Normalize took 3.73 s cold against 1.03 s repeated in a
14-stream process, 4.72 against 2.21 s in a 56-stream one, and 4.17 against 1.19 s with large pages off; first-ask
misses (a class lookup of a term not looked up before, a verdict not evaluated before) are 88%, 84% and 88% of those
gaps. In the quietest run (all 56 streams once, 4 growths after 2 as a sweep orders them) normalize is 11.76 s of a
45.97 s build (25.6%). Its misses are 6.78 s (14.8%): lookups 0.63, evaluating verdicts 5.10 (bitwise checks 2.58, of
it building their exhaustive input memos 1.00; tree searches 2.52), and inserting verdicts with their
`CLASS_UNUSABLE` lines 1.05 (the print 1.04 for 10,236 lines, about 100 µs a line). Its hits are 4.98 s, 187 ns a node
over 26.64 M node visits (9.5 per distinct argument). A miss is a term no earlier build asked: the 4-growth builds ask
again every one of the 240,332 terms the 2-growth builds missed first, and the same 14 streams built inside a 56-stream
process take 14% fewer lookup misses and 28% fewer verdict evaluations than alone. The rest of the spread is the hit
path, 156-437 ns a node between runs; in run `-twice-all56` builds that took 10,000 page faults or more ran it at
678-802 ns a node against 228-275 for builds under 1,000 (time-weighted, a few builds at 3-4 µs dominate), while
normalize itself took 4 of the 4.99 M faults. That mechanism is not tested. The shares are of a build before `cd7dacb`
(4.9% less work); the miss times do not depend on it. Levers, none built then (`PARKED.md`, "Cheaper first asks in
the stream builds"): batching the `CLASS_UNUSABLE` lines (1.04 s, 2.3% of the build); building `bitwise_holds`'
exhaustive inputs once per process (1.00 s, 2.2%; F3 in the survey below, landed 2026-10-29); a normal-form memo per
term in `stream_laws` (cleanup plan CU16, decided against 2026-10-27, F1 below, landed 2026-10-29), which would
remove most of the hit path (4.98 s, 10.8%); verdicts and lookups carried across processes (5.73 s, needs a stored
format). Not measured: `carry_cap` reads `CARRY_CAP` through `Setup::var` (a string-keyed map and a lock) on each of
the 4.49 M steps that have a representative.

*Deriving the 2-growth sequence from the 4-growth build (survey, 2026-10-28; nothing built).* A sweep's parent builds
both before any loop starts, the 2-growth one first (`scope_extras` calls `served_laws`, hence `window`, before
`stream_sequence` at `held_levels`; `crates/church-bv/src/driver.rs`), on 4 threads each; its children read law files and
build nothing. Filtering the merged 4-growth sequence to depth 2 does not give the 2-growth one: `build_sequence`
merges round-robin by position within each stream, and a stream's 4-growth list is 1.5-7.0 times its 2-growth list
(median 3.0 over the 54 non-empty streams), so positions differ. (Streams [x1 at depth 3, x2, x3] and [y1, y2 at depth
3] merge to x1 y1 x2 y2 x3, which filters to y1 x2 x3, while the restricted streams merge to x2 y1 x3.) An exact
derivation keeps each stream's list with each law's depth (`level[a].max(level[b])`, already computed in
`stream_laws`) and merges the restricted lists, each of which is the stream's 2-growth list by the nesting above. The
saving is bounded by the 2-growth build: 6.5 of the 22.8 s both builds took under samply in run
`2026-10-28-class-ids-prof` (after `cd7dacb`), and 12.4% of the busy samples at a join budget of 100 (run
`2026-10-28-mjv-prof`, before it). Part of that only moves into the 4-growth build, which asks again every term the
2-growth build missed first (above): on 14 streams a first 2-growth build took 8.27 s against 5.73 s repeated
(`stream_probe_overhead`), so about 69% of it is saved outright; not counted. It saves nothing where the two salts
differ (`GEN_DRAW` set), in processes that build only 2 growths (`ABLATE=gen`, `LOOP_MODE=none`, `ROUNDS=0`), or
when the shallow sequence is asked first; `regenerate_held` would go from four builds to two (salt 1 at 2 growths
stays). The nesting was probed only at salt 1, on 3662451's copy of the build. Landed 2026-11-08 as option (c), one
call for every depth (`streams::stream_sequences`, used by `scope_extras` and `regenerate_held`): the restricted lists
equal the shallow ones at salts 0, 1 and the held salt (`a_deeper_stream_restricted_is_the_shallow_one`), the full
pins hold, and the pin test's parent now logs one build per salt (63.2 s and 30.2 s at 78% machine load, run
`2026-11-07-o2-pins2`). The pin test's retired instructions fell 19.9%, 1075.0 G to 861.1 G best of 2 (medians 1075.6 G
and 862.7 G; each arm's two runs within 0.4%; one batch per arm, since each arm's first batch hit icount's 900 s limit
while another session's gate loaded the machine; run `2026-11-07-o2-count`; a rotated rerun of the same exes, 4 batches of 2 in ABBA order, gave batch medians of 1073.0-1078.3 G and 858.3-859.7 G, 20.0% between the medians of those, 19.9-20.4% over any pairing, run `2026-11-08-o2-count-rot`), close to the bound above (6.5 of 22.8 s,
69% saved outright, about 20%). Found on the way: `scope_extras` built the 4-growth sequence even with
`EXTRAS_N=0`, where it takes no law from it; since 2026-11-08 it skips the build when a mine takes none.

*Survey: the open-law filter, `Term::show` and mimalloc's purge (2026-10-29, profile `2026-10-29-zerofill3-prof` of the
pin test at `c8c2e68`; read-only, each finding re-checked by a second agent told to refute it; nothing built for it,
the "P1 spike" below came after).* Shares
are of the profile's 56,466 busy samples: the two sequence builds alone (the 4-growth one about three quarters of
them), on 4 stream threads, so they are time, not work. Lock, allocator and stall time weighs more in samples than in a
count of instructions at one thread, and every instruction figure below but the P1 spike's is an estimate, not a
count. In a sweep at a join budget of 100 the two builds were 46% of the busy samples (run `2026-10-28-mjv-prof`, before
`cd7dacb`). The splits reproduce from the run's folder (`pcs.json.gz` with the `pcs.json.syms.json` beside it, the exe
copy and its PDB; `llvm-symbolizer` on `PATH`) with `docs/runs/2026-10-29/scripts/`
`filter_split.py <dir> <exe>` (the filter's samples by kind of work) and `callers.py <dir> <exe> <frame>... [--with
<frame>...] [--without <frame>...]` (the samples holding any of the frame prefixes, by caller). Options have ids (F, S,
P) for the order chosen at the end, and their points overlap, so they do not add: 3.0 of the plans built (6.14, most
of F2's bound, inside F1's 17.63) are the purge sweep P1 removes (`_mi_arenas_collect`; 2.6 of it in
`mi_arena_try_purge`'s own frame, 2.5 of that the stall), F1 shrinks what F2 acts on, and S1 and S3 share the sorts.

*The filter (`stream_laws`' `scoped` closure, 45.41%).* `Classes::normalize` is 38.48: 20.85 on a term's first ask
(verdicts: tree searches 8.92, `bitwise_holds` 9.56, of it building exhaustive inputs 4.26, filling vectors 3.50 and
comparing them 1.80; other verdict work 0.17; class lookups 2.20) and 17.63 on every visit (plans built 6.14, lookup
hits 5.23, drops 0.27, the walk and the rest 5.98). `shuffled` is 3.58, the width-8 refuter (`r8.agree`) 2.69
(filling 1.40, comparing 1.29), the closure's own drops 0.63 (`Rc` drops: the plan is the one `Rc` it gets back from
`normalize`) and the rest 0.03. The causes:
- `pool_conjectures` pairs every member of a group with its head (`(g[0], t2)`), so the filter normalizes the head once
  per conjecture. A 4-growth build makes 26.64 M node visits for 2.797 M distinct arguments (run
  `2026-10-28-normalize-cold-distinct`): 12.18 M of operator nodes, 4.4 per distinct argument, from the repeated heads
  and from subterms shared across terms (the log does not split them), and 14.46 M (54%) of leaves, of five kinds
  (`NODE` and `NODE_OP` in the raw `out.log` of run `2026-10-28-normalize-cold-once-all56`).
- `normalize` builds a plan at every node (`Plan::refl`, `cong`, `trans`), and the filter reads only the normal form.
- `bitwise_holds` builds up to five exhaustive input memos (widths 1-5, `k` vectors each) per call: all five unless the
  sides differ at a narrower width, which is rare here.
- `first_difference` compares element by element (`(0..tries).find(|&i| x[i] != y[i])`).
- `shuffled` formats a `String` per law to hash it.

`normalize`'s normal form is a pure function of the table, `n`, `k`, the carry cap and the term (`step`, `verdict` and
`tree_encoding` are pure in their keys), and `r8` is a cache. `normalize` also records each step in `job.table_steps`
and builds a real plan unless `job.rules().score_only`; `stream_laws` never reads `table_steps` back and drops every
plan unread, so no memo or reordering of this work can change the laws. Options, in points of busy samples:
- **F1.** A normal-form memo per `stream_laws` call (a memo parameter on `normalize`, leaves answered without it):
  about 9-13. The 2.28 M top-level calls (both sides of each of the 1,139,766 grown laws) and the two child calls of
  each of the 2.797 M evaluations remain, 7.87 M of the 26.64 M visits, so at equal cost per visit it saves
  17.63 × (1 - 7.87/26.64) = 12.4. These are the 4-growth build's counts (its 2.797 M distinct arguments summed over
  its 56 `stream_laws` calls, each counting its own), applied to both builds' points; over both builds 30.0% of the
  visits remain, 12.3, and the ranges below become 9.1-12.2 and 11.8-12.7. Two corrections, neither counted, pull
  opposite ways. The visits that remain are at most half leaves (only a law's head can be one, and every evaluated
  node but the few whose children are both leaves has an operator child), against 54% of all of them, so the visits
  removed are the cheaper mix: 9.2-12.3 if a leaf costs 0.3-0.5 of an operator visit (the low end if none of the
  visits that remain is a leaf, the high end if half are). And of the calls that remain only the 2.797 M evaluations
  do a visit's work; the others that are not leaves (1.1-5.1 M) are memo hits, one probe each: with both corrections,
  leaves at 0.3-0.5 and a hit at half an operator visit, 11.9-12.8. Neither figure charges the 2.797 M misses' probes
  and inserts. About 1.6-2.2 of F1's saving is the purge sweep under the plans built (P1: its 3.02 points there, times
  the saving's 52-73% share of the 17.63). `normalize`'s present hit path (the per-visit work on a term already seen:
  the `lookup` lock, hashing, plan allocation) is 10.8% of a quiet one-thread 4-growth build's time before `cd7dacb`
  ("Why normalize is slow on a cold stream"), and F1 removes most of it; that path's share of instructions is
  probably smaller (3-5%, an estimate). `Term::op` counts `Site::Op`, so the `op` totals of this workload's WORK lines
  drop with it. `table_steps`, a set of distinct pairs, would not change: a memo hit only skips a `step` the same job
  already took, and nothing wraps `normalize` in `steps_if_closed` (its one non-test user, the kernel-check task, and
  its tests wrap `rewrite_plan`, which takes class-table steps itself, or bare inserts). A memo shared across
  `steps_if_closed` calls would change it: a closed law's call would not retake the steps an earlier open law's call
  took and dropped. It was the memo half of `PARKED.md`, "Build the stream sequence lazily, only as far as it is
  read" (cleanup plan CU16). Landed 2026-10-29 ("F1 landed" below): -17.3% in a count.
- **F2.** Counting mode for the filter (`job.with_rules(job.rules().counting(true), ..)`, as the test
  `counting_and_compiling_agree` runs it; "Scoring builds no plans"): at most the plans built (6.14, 3.0 of it the
  purge sweep P1 also removes) and the plans' drops (about 0.8: the `Rc` drops, 0.18 inside `normalize` and 0.63
  after it). Once F1 lands the plans built scale with the visits that remain: at most 1.8 at equal cost per visit
  (less if a memo hit builds no plan), 0.9 with P1's sweep gone. Landed 2026-10-30 ("F2 landed" below), as a
  plan-free `normalize` rather than counting mode: -2.4% in a count.
- **F3.** `bitwise_holds`' exhaustive inputs built once per process, shared by the threads and keyed by `(w, k)` (a
  `OnceLock`; `ValueMemo` owns its `vars`, so they would sit behind an `Arc` or a static slice): 4.26. The probe above
  measured them at 1.00 s of a 45.97 s one-thread build (2.2%, "Why normalize is slow on a cold stream"), so expect a
  count saving nearer that 2.2% than these 4.26 points of time at 4 threads. Both callers gain (`verdict` and
  `prove_eq`'s per-position step). It is one piece of `PARKED.md`, "Cheaper first asks in the stream builds".
  Landed 2026-10-29 ("F3 landed" below): -13.3% in a count, far above this estimate.
- **F4.** `first_difference` compares the slices whole first (`x[..tries] == y[..tries]`, a `memcmp` for `u8` and
  `u128`) and scans only where they differ: the compare loops are 3.09 (bitwise 1.80, refuter 1.29). Not tried before.
  Landed 2026-10-29 ("F4 landed" below).

Rejected: refuting first, since `r8.agree` would run on every grown law instead of the open ones: 4.6 times as many at
4 growths (1,139,766 against the 246,721 that `normalize` leaves open) and 7.2 at 2 (449,962 against 62,864; run
`2026-10-28-stream-probe`), 5.1 over the profile's two builds (1,589,728 against 309,585). So the refuter's 2.69 points
grow by at most 4.1 times themselves, about 11 more (5.3 for the compares, which scale with the laws; up to 5.8 for
the fills, which grow with the distinct terms), to skip `normalize` for the 0.9% of grown laws it refutes over the two
builds (1.1% at 4 growths; about 0.35); a
process-wide normal-form memo on top of F1 (0.7-1.4 points, an estimate, for a lock per visit); a memo of
`tree_encoding`'s raw tables (about 2 if half the calls repeat, not measured; all of `raw_table` is 4.08).

*`Term::show` (11.00%; 16.28% with the `sort_by_cached_key` frames that use it as a key).* By caller: the pool sort
(`terms.sort_by_cached_key(|t| (level[t], t.show()))` in `stream_laws`) 5.43, the conjecture sort in
`pool_conjectures` 3.05, `shuffled`'s hash 1.82, the pin test's digest 0.44, the seeds sort 0.23, the `CLASS_UNUSABLE`
lines 0.02; with the sorts' own frames, `stream_laws`' two sorts are 8.11, `pool_conjectures` 4.13 and `shuffled`
3.58 (`callers.py` with `church_bv::rewrite::Term::show`, then with `alloc::slice::impl$0::sort_by_cached_key` added).
Each call grows a `String` from empty (`show_into`): about 16.1 M calls over both builds (the seeds, each pooled term,
both sides of each conjecture and of each shuffled law, and the digest; the counts of run `2026-10-28-stream-probe`),
about 0.39 µs each at 4 threads (11.00% of 56,466 samples at 1 ms each). `shuffled` and the digest hash the string
once and drop it; the sorts keep every key until the sort ends, and a term's key is an operand in about 2·log2(n) of a
sort's n·log2(n) comparisons (2.05 points of `String` compares in the sorts' own frames: `callers.py` with the sort
frame, `--with 'alloc::string::impl$84::cmp' --without church_bv::rewrite::Term::show`). The text order is the
lexicographic order of the terms' preorder tokens ranked as text (`-1`, `0`, `add(`, `and(`, `lt(`, `or(`, `p`, `q`,
`shl1(`, `shr1(`, `sub(`, `u`, `v`, `w`, `x`, `xor(`, `y`, `z`): equal token prefixes give equal text prefixes, and the
one token that is a prefix of another, `x` of `xor(`, is followed by `,`, `)` or the end, all below `o` (checked on
every term to size 5 and 47k random terms to size 17 by `docs/runs/2026-10-29/scripts/text_order_check.py`). Options:
- **S1.** A structural `show_cmp` (token ranks compared in preorder, no strings), and the seeds, pool and conjecture
  sorts by it (the pool sort over `(level, term)` items, with no `level` lookup inside the comparator). One mechanism
  for every text-order site: this workload's three sorts and, outside it (no samples here), the rewriter's four
  `show_cmp` uses, with no change of order or contract; the miner's and the table tests' sorts by `show()` could
  follow. Unlike the structural operand order rejected in "Miner speedups", it is the same text order, so no mined
  library moves. The keys' `show` calls are 8.71 points (5.43 + 3.05 + 0.23) and the sorts' own frames 3.53
  (8.11 + 4.13 - 8.71; 2.05 of it `String` compares). In their place each of the n·log2(n) comparisons walks two
  terms through interned nodes as far as their first differing token: the formats and key allocations go, but misses
  on scattered nodes, which a count does not see, are new. So the saving (5-10 points, an estimate; at most 10.2 =
  8.71 + 3.53 - 2.05 if a comparison costs no less than a `String` compare does now) needs a profile. The test
  `show_cmp_is_the_text_order` checks only the first 2000 representatives in text order; its replacement should
  compare against every term to size 5 and a sample of all representatives. Landed 2026-10-29 ("S1 landed" below):
  -1.5% in a count and about 1.8 points, all in the conjecture sort; the pool sort costs what it did. `show_cmp` itself became `Term`'s `Ord` and the miner's and tests' string-keyed sorts followed ("Ord landed" below).
- **S2.** `shuffled` hashes without a `String`: `show_into` writes through `fmt::Write` into the FNV state, the same
  bytes in the same order, so the same permutation: about 2 (an estimate: 2.02 of `shuffled`'s 3.58 have a mimalloc
  (`mi_`, `_mi_`), `church_bv::_::__rust_` or `alloc::raw_vec::` frame on the stack, 0.35 of them the purge sweep;
  with purge off those are 1.21 of 2.80 (run `2026-10-29-purge-spike-prof`), so after P1 nearer 1.2; the walk and
  the hash stay). If the test's digest also streams into its FNV state, up to 0.35 there (its 0.59 less the walk and
  the multiply; 0.20 by the same frames). Landed 2026-10-29 ("S2 landed" below), with `classes::text_hash` on the same
  writer: -2.2% in a count (one quiet pair) and 5.0 points of time share, above the estimate.
- **S3.** Drop the conjecture sort by making `shuffled` a total order (hash, then text), and take each group's head as
  its minimum instead of sorting the pool; the seeds sort stays, since its order picks the terms the growth samples.
  At salt 0, `RULEMINER_SHUFFLE`'s default, `shuffled` keeps the conjecture sort's order, so there the conjecture
  sort stays, either in `pool_conjectures` or moved into `shuffled` after the filter, on the grown laws only
  (1,139,766 of 1,838,265 conjectures at 4 growths, 449,962 of 851,901 at 2), roughly 40-50% less of it; the
  pool-sort half applies at any salt. The pins (salt 1) do not cover salt 0, which needs its own check. At most about
  7 more after S1 if S1 saves 5 (the low end of its range), about 2 if it saves 10: S1 and S3 together cannot exceed
  the three sorts' 12.24 points (8.11 + 4.13) less what is left of the seeds sort, before the cost of the minimum
  scan. It changes `pool_conjectures`' contract (it keeps its sort when `cap` is nonzero, since
  `laws_survive_a_law_file` samples by stride over it; only `stream_laws`' `cap` 0 call drops it) and
  `shuffle_is_a_fixed_permutation`. Landed 2026-10-29 ("S3 landed" below), further than surveyed: `cap` went too (the
  one stride-sampling caller does it inline), and the counts fell 9.4% and 4.6% against the survey's "at most about 7".
- **S4.** Presize `show`'s `String` to `5 * size - 3` (an upper bound, reached by terms of only shifts and `-1`): about
  2.5-2.9 (an estimate: the 2.95 of `show`'s samples holding a mimalloc or `church_bv::_::__rust_` frame, less the
  0.25 of the first allocation, which presizing keeps; the 4.09 holding `::reserve::do_reserve_and_handle` include
  the growth logic too and are an upper bound), mostly covered by S1 and S2. Decided against 2026-10-29: after S1 and
  S2, `Term::show` is 0.03% of the pin test (run `2026-10-29-s2-prof`); what calls it now is outside this workload.

Rejected: caching each term's text (about 0.7 GB, an estimate); a structural hash in `shuffled`, which changes the
permutation and so both pinned sequences.

*mimalloc's purge (4.95% inclusive).* `_mi_arenas_collect` is 4.95, `mi_arena_try_purge` 4.80 inclusive and 3.79 self,
with 95% of the self samples on the instruction after its first load (`arena->memid.is_pinned`): a stall, not work.
`VirtualFree` is 0.92, recommits 0.04. It runs only in the 4-growth build: none of `mi_arena_try_purge`'s samples in
the run's first 6 s (seconds counted from the profile's first sample; 15 of `_mi_arenas_collect`'s, all at its entry,
12 of them the clock read), 2.5% of second 6 (nearly all `VirtualFree`) and none of second 7, then 5-19% of each whole
second's busy samples from 8 s to the end at 16 s (`_mi_arenas_collect` inclusive; `mi_arena_try_purge` self 4-17%).
The mechanism (mimalloc v3.3.2 from `libmimalloc-sys` 0.1.49, `v3/src/arena.c`): a free into an arena that is not
pinned (large-page arenas are) schedules a purge `purge_delay` (1 s) out and sets the process-wide expiry if none is
set. Once that expiry passes, every
`_mi_arenas_collect` (on a page abandoned or freed, and on a heap collect) that wins a one-thread guard (the others
return at once) visits the arenas (`mi_arenas_try_purge`), stopping once a quarter of them plus one have purged. Only a
visit of every arena that finds none purged and none with its own expiry still pending clears the process-wide expiry,
which steady freeing does not allow: some arena always has one pending. The "at most one purge per delay cycle" store
(`now + delay/10`) runs only when the expiry is set and not yet passed: the unforced calls (a page abandoned or freed,
the periodic collect) have ruled that out, and only the forced or visit-all ones (`mi_collect(true)`, thread and
process exit), rare here, can reach it. The self share swings between profiles of the same loops: 0.5% in run
`2026-10-28-class-ids-prof`, at most about 0.6% in `2026-10-28-zipword-prof` (absent from its top 40), 3.8% in
`2026-10-29-typedrows-prof` and here. A reading, not checked: the build turns large pages on (`.cargo/config.toml`; a
sweep's children turn them off), so how many arenas get large pages decides the share. As work, the sweep was
guessed at 0.1-0.5% of the run's ~300 G instructions (not derived: its samples are mostly one stalled load); the "P1
spike" below found purging adds none to the runs that count lowest. Three earlier probes with purging off
(`MIMALLOC_PURGE_DELAY=-1`) tied: a sweep's time and faults ("Survey: the OS kernel's 22.8%"), kernel time
("Kernel scaling and the id arena") and faults (`docs/superpowers/specs/2026-09-30-bitvector-interface-design.md`,
"Allocator purge is not it"). A fourth, with
immediate purging (delay 0), left the miner's peak commit unchanged (run `2026-10-23-miner-mem-purge0`). None tested
this workload's time: the sweep's probe set it only for the children, which run 28-68 ms each, so the 1 s delay never
fired; the kernel-time probe read the accounted kernel/user split of a ~3 s `proof_cost_split`, which that section
finds unreliable (total CPU stayed 2.70-2.91 s); the third counted faults in an n=512 scoped check; the fourth had no
delay and measured memory. Options:
- **P1.** Purge off in the harness (`mi_option_set(purge_delay, -1)`: the sweep returns at once and `_mi_os_purge_ex`
  decommits nothing, so `mi_collect(true)` returns no memory either), through a typed binding for the functions:
  `libmimalloc-sys` as a direct dependency with its `extended` feature, replacing the hand-declared `mi_collect`
  (`classes.rs`) and `mi_option_get` (`machine.rs`), which a third declaration would otherwise join (`PARKED.md`,
  "Class-table loose ends"). The crate has no constant for `purge_delay` (or `arena_reserve`), so its id, 15 in v3's
  enum, stays a literal, while its `mi_option_large_os_pages` replaces `machine.rs`'s `6`. Memory is no longer
  returned after the class build, so it stays out of the product. Estimated before the spike at up to 4.95 points of
  time and, in instructions, the sweep's 0.1-0.5% plus the decommits' and refaults' kernel work; measured in the "P1
  spike" paragraph below (no instructions saved in the runs that count lowest, less spread in the counts, the sweep
  gone from the profile, busy samples down 8.9% and untimed times 5.8% and 10.6%, a direction only).
- **P2.** `arena_reserve` at 256 MiB instead of the build's 64 MiB (`mi_arena_reserve` reads the option at each
  reservation, so unlike large pages it can be set at run time, for every arena after the first, which the runtime's
  first allocation reserves before the test runs; sizes double every 8 arenas): about 11 arenas to visit instead of
  about 22 if the run reaches 3 GiB of arenas (its size is not measured), about 2 points of time (the 3.79 self stall,
  if it scales with the arenas visited). "Allocation schemes against the size cost" found 256 MiB tied 64 MiB on CPU
  only on a ~3 s `proof_cost_split`, shorter than the 6 s this profile ran before its first sweep and not checked for
  sweeps, with 192 MB more peak private memory (1090 against 898 MB).
- **P3.** Patch mimalloc to set the expiry to the earliest pending one instead of leaving it stale (about 6 lines of
  C, through `[patch.crates-io]` or upstream): it keeps purging, removes the sweep and leaves `VirtualFree`.

*Order chosen (2026-10-29).* P1 first, as a throwaway spike: a profile with purge off, and counts of the same exe in
batches with purge on and off (if purging causes the batch-to-batch drift, it vanishes with purge off, and every later
count A/B tightens). Then F4, F3 and F1; then S1 and S2. Each keeps both pinned sequences byte-identical and gets its
own count A/B. F2, S3 and S4 wait on the options before them, and P2 and P3 on whether P1 lands (`PARKED.md`, "Options
held behind the filter, `show` and purge survey").

*P1 spike (2026-10-29, throwaway, reverted).* One exe, the `c8c2e68` code with
`docs/runs/2026-10-29/patches/purge_spike_on_ab9eeba.patch` (on `ab9eeba`; `PURGE_OFF` in the exe's `.env` sets
`purge_delay` to -1 at the test's start), run with purge on (A, the 1 s default) and off (B). Both sequences stay pinned
with purge off at one stream thread (run `2026-10-29-purge-spike-pin-B`; A in `-pin-A`) and at four (`-prof`), so
`c8c2e68`'s fill gives the same sequences when no freed page is returned to the OS and refilled with zeros (on these
runs; not a proof for every path). Counts (runs `2026-10-29-purge-spike-icount-*`, 4 rounds of 3 runs per arm in two
batches, A B B A then B A A B; `docs/runs/2026-10-29/rows/2026-10-29-purge-spike-icount.txt`): the best runs tie
(298.66 G against 298.68), so purging adds no instructions to the runs that count lowest, but the purge-on rounds spread
more: medians 299.16-304.86 G (a range of 1.9%) against 299.14-301.31 (0.7%), pooled (median - best) / best 0.016
against 0.003. Purge off's 0.7% range is mostly the one round that started at 47% machine load; without it the
purge-off rounds span 0.18%. The purge-on arm had loaded starts too (28% and 35%), so the arms are not load-matched;
among the rounds that started at 14% load or less (2 with purge on, and purge off's same 3), purge on spans 1.40% and
purge off 0.18%. With so few rounds this suggests that purging adds spread; it does not show how the 0.7-0.9% drift
between batches ("Landed with both checks" above) splits between purging and load. A reading, not checked: purging
is timed (the 1 s delay), so a run slowed by load purges and refaults more for the same work. Purge off drifted less
from the first batch to the second (best +0.08%,
298.68 to 298.91 G, pooled median +0.23%, against +1.20% and +1.15% with purge on), but that is one pair of batches,
with second-batch rounds starting at 28% and 35% load with purge on and 14% and 47% with it off, so it has not been
shown to make batches comparable; count A/Bs still need interleaved rounds in one batch. The profile with purge off (run
`2026-10-29-purge-spike-prof`, `docs/runs/2026-10-29/rows/2026-10-29-purge-spike-prof.txt`): the sweep is gone
(`_mi_arenas_collect` 4 samples against 2,797, 4.95%); the plans built fell from 3,469 to 1,758 samples, about the 1,707
of the sweep under them; busy samples fell 8.9% (51,413 against 56,466), of which 2,793 are the sweep and about 2,260
are not attributed (about 1,800 of those outside the filter). Time, from untimed pairs only: 39.68 against 42.12 s at
one stream thread (-5.8%, the pin runs back to back), 14.41 against 16.12 s at four (-10.6%, against
`2026-10-29-zerofill3-prof`, the unpatched `c8c2e68` exe six hours earlier, and more than the busy samples fell), so
both give a direction only, and a time claim needs a timed A/B. P1 itself is held for the user's call (`PARKED.md`,
"Options held behind the filter, `show` and purge survey").

*P1 timed (2026-10-30, env var only, no code change).* The F2 build (`1a37507`'s code) at one stream thread pinned to
CPU 8, three arms alternated over 8 clean rounds by `runs time` under `run.ps1 -Timed` (run `2026-10-30-purge-time3`;
`docs/runs/2026-10-30/rows/2026-10-30-purge-time.txt`): A the default purge, B `MIMALLOC_PURGE_DELAY=-1`, A2 the default
again. Job CPU medians 25.97 s (A), 24.45 (B), 26.31 (A2); B - A median -1.90 s (-7.3%), B ahead in 8 of 8 rounds,
in either order (-0.82 s running first, -2.76 second); wall -1.79 s (-6.8%). The A/A reads +0.34 s (+1.3%), ahead in 3
of 8 rounds, within -1.03 to +1.25 s; B's rounds run -0.72 to -5.02 s, five of them past the A/A's -1.03 and the
other three (-0.72 to -0.88) inside it, all eight on B's side. Memory
cost on this workload: peak process memory 2564-2568 MB in all 24 runs, peak working set 1896 MB (B) against 1885
(A): +11 MB, three of B's rounds near 1928. With purge off the suite passed (168 tests, 31 ignored) and both salt
pins held (runs `2026-10-30-purge-off-{suite,pin,pin0}`). Not measured: four stream threads (the untimed spike gave
-10.6% there), processes that run longer than the pin test (the miner, sweeps), `MIMALLOC_ARENA_RESERVE` (P2) on top.

*F4 landed (2026-10-29).* `first_difference` compares the vectors' first `tries` entries whole (`x == y` on the two
slices, a `memcmp`) and scans for the first differing input only when they differ. The test `value_memo_matches_interp`
now also runs 2 tries (the corners alone, where many distinct terms agree), so a version that compares past `tries`
fails it; at 16 and `SCREEN_INPUTS` tries that mutation survived. The church_bv suite passed (163 tests, 30 ignored;
run `2026-10-29-f4-suite`) and both sequences stay pinned (run `2026-10-29-f4-pin`). Counts against `c8c2e68` in one
batch (runs `2026-10-29-f4-icount-{L1,F1,F2,L2}`, rounds L F F L of 3 runs at one stream thread, purge on;
`docs/runs/2026-10-29/rows/2026-10-29-f4-icount.txt`): -7.9% at the best runs (274.66 G against 298.23), -10.1% at the
pooled medians (275.54 against 306.35), every F run below every L run. L's round medians drifted 2.3% (308.51 then
301.46 G) and F's 0.26% (275.03, 275.74), both with purge on, so purging does not widen every pair of rounds (P1 spike
above). The profile after it (run `2026-10-29-f4-prof`, `docs/runs/2026-10-29/rows/2026-10-29-f4-prof.txt`; untimed:
59,291 busy samples at 13% load against 56,466 at 8%): `ValueMemo::agree` 4.9% inclusive (7.9 before), `bitwise_holds`
7.7 (9.6), `verdict` 16.8 (18.7), the filter 43.2 (45.4); `pool_conjectures` 30.1 (28.4), `Term::show` 11.0 (11.0),
`ValueMemo::exhaustive` (F3's target) 4.2 (4.3), `mi_arena_try_purge` 4.3 self (3.8). `agree` and `bitwise_holds` lost
about 1,560 and 840 samples, together 4.2% of the earlier profile's, though its total was lower: the survey's 3.09
points for the compare loops was too narrow. The rest of the gap to the count's 7.9% is a reading, not checked: a tight
scalar loop retires many instructions per cycle, so its share of instructions exceeds its share of time.

*F3 landed (2026-10-29).* `ValueMemo::exhaustive` takes its inputs from a `SharedMemo` keyed by width and variable
count (`EXHAUSTIVE_INPUTS`, the pattern of `stream_sequence`'s `MEMO` and `machine.rs`'s `TREE_ENCS`), built once per
process and shared as an `Arc<[Box<[u8]>]>`, so every caller gains: `bitwise_holds` (up to five widths per call), the
refuter's `e4` and `e3`, `pool_conjectures` and the miner's pool. `ValueMemo::new` takes that `Arc`; a static slice
would have needed an entry on `job.rs`'s `PROCESS_WIDE` list or leaked the other callers' inputs. The test
`exhaustive_inputs_are_built_once` failed before the change (two calls, two allocations); the church_bv suite passed
(164 tests, 30 ignored; run `2026-10-29-f3-suite`) and both sequences stay pinned (run `2026-10-29-f3-pin`). Counts
against `cc95d83` in one batch (runs `2026-10-29-f3-icount-{L1,F1,F2,L2}`, set up as F4's;
`docs/runs/2026-10-29/rows/2026-10-29-f3-icount.txt`): -13.3% at the best runs (243.11 G against 280.54) and at the
pooled medians (244.02 against 281.39), every F run below every L run, each arm's two round medians within 0.33%. The
survey expected nearer 2.2% (the probe's 1.00 s of a 45.97 s one-thread build). A reading, not checked: the inputs are
a tight loop over up to 37,448 entries per variable (widths 1-5 at three variables), which retires many more
instructions per sample than the filter's hashing and pointer chasing. The same L exe counted 274.66 G best in F4's
batch about 1.5 hours earlier, +2.1% now at lower load (6-14% at the rounds' starts against 18-30%), so the drift
between batches is not load alone. The profile after it (run `2026-10-29-f3-prof`,
`docs/runs/2026-10-29/rows/2026-10-29-f3-prof.txt`; untimed: 53,184 busy samples at 6% load against 59,291 at 13%):
`ValueMemo::exhaustive` 0.04% inclusive (4.2 before), `bitwise_holds` 3.6 (7.7), `verdict` 13.2 (16.8); the filter
43.1 (43.2), `pool_conjectures` 28.9 (30.1), `Term::show` 12.0 (11.0), `shuffled` 6.2 (4.0), `Plan::new` 5.8 (6.7),
`mi_arena_try_purge` 4.5 self (4.3), `SharedMemo::lock` 1.2 (1.2).

*F1 landed (2026-10-29).* `Classes::normalize` takes a `NormalForms` map (an operator term to its normal form and plan)
and answers an operator node asked again from it; a leaf is stepped, not looked up. `stream_laws` makes one per call
inside its `scoped` closure; the tests that call `normalize` pass their own, one per rules mode in
`counting_and_compiling_agree`, since the plans are the job's. The test `normal_forms_are_memoized_per_operator_node`
(a term asked again gets the memo's plan, by `Rc::ptr_eq`; each normal form equals a fresh memo's; the memo holds every
operator subterm asked and no leaf) failed to build before the change. The church_bv suite passed (165 tests, 30
ignored; run `2026-10-29-f1-suite`) and both sequences stay pinned (run `2026-10-29-f1-pin`, whose lines equal F3's pin
run's once sorted, the 14,536 `CLASS_UNUSABLE` lines included). Counts against `37e1e64` in one batch (runs
`2026-10-29-f1-icount-{L1,F1,F2,L2}`, set up as F4's, L rebuilt from a clean worktree at that commit;
`docs/runs/2026-10-29/rows/2026-10-29-f1-icount.txt`): -17.3% at the best runs (197.96 G against 239.49) and -17.1% at
the pooled medians (199.20 against 240.14), every F run below every L run, each arm's two round medians within 0.64%.
The profile after it (run `2026-10-29-f1-prof`, `docs/runs/2026-10-29/rows/2026-10-29-f1-prof.txt`; untimed: 48,235
busy samples at 18% load against 53,184 at 6%) splits the filter (`filter_split.py`, on both profiles; sample counts
from its shares, so about): the work on every visit 4,460 samples against 10,100 in `2026-10-29-f3-prof` (plans built
670 against 3,070, lookup hits 1,230 against 3,530, the walk and the rest 2,530 against 3,370), first asks 8,070
against 8,300, and the closure's drops 760 against 310, now mostly the memo's table (`hashbrown::raw::impl$17::drop`,
1.56%). Net of the drops that is 5,190 samples, 9.8% of the earlier profile's, inside the survey's 9.1-12.2 for both
builds; the work on every visit kept 44% of its samples, not the 30% of visits that remain, since the survey's figures
charge nothing for the misses' probes and inserts. Shares: the filter 35.6% inclusive (43.1 before),
`pool_conjectures` 33.3 (28.9), `verdict` 14.3 (13.2), `Term::show` 13.0 (12.0), `shuffled` 6.2 (6.2), `Plan::new` 1.4
(5.8), `mi_arena_try_purge` 2.6 self (4.5). F2's bound is now the plans built, 1.4 points, and the part of the memo's
drop that is its `Rc`s (counting plans are one shared `Rc`, so their drops would be decrements): its trigger, a profile
after F1 that still shows plans built, is met (landed 2026-10-30, "F2 landed" below, which also replaced this
paragraph's `NormalForms` of terms and plans with terms alone).

*S1 landed (2026-10-29).* `Term::show_cmp` compares two terms by structure: equal operator heads recurse into the
operands, and the first differing head decides by its token's text, so the order is the `show()` text's with no string
built. It replaces the version that wrote both terms into two thread-local `String`s (`BUFS`, dropped from
`hidden_state_is_classified`'s `THREAD_LOCAL` table), and the seeds, pool and conjecture sorts use it
(`sort_unstable_by`; the pool sort over `(level, term)` items). The test `show_cmp_is_the_text_order` checks it against
the text order on every pair of terms to size 3, and checks that a sort by it is the text sort, each term below the
next, on every term to size 5 and on every class-table representative. The church_bv suite passed (165 tests, 30
ignored; run `2026-10-29-s1-suite2`, after `2026-10-29-s1-suite` failed `hidden_state_is_classified` on the dropped
static's row) and both sequences stay pinned (run `2026-10-29-s1-pin`). Counts against `c19ef00` in three batches (runs
`2026-10-29-s1{,b,c}-icount-{L1,F1,F2,L2}`, set up as F4's; `docs/runs/2026-10-29/rows/2026-10-29-s1-icount.txt`;
s1b's L1 is invalid, a re-count of an old trace): -1.5%, -1.3% and -1.6% at the best runs, single runs overlapping at
loads up to 42%. The profile after it (run `2026-10-29-s1-prof`, `docs/runs/2026-10-29/rows/2026-10-29-s1-prof.txt`;
untimed: 49,229 busy samples against 48,235 at about the same load) finds the saving in the conjecture sort alone. By
caller the sorts are `pool_conjectures` 2.96 (4.87 in `2026-10-29-f1-prof`), `show_cmp` 2.72 of it, where the keys'
`show` calls were 3.57 and the `String` compares 0.80; and `stream_laws` 9.60 (9.52), `show_cmp` 8.61 of it, where the
keys were 6.53 and the compares 1.64. So about 1.8 points net, well under the survey's 5-10: in the pool sort the
structural compare costs what the keys and compares did. A reading, not checked: the pool's terms share long
prefixes, and the walk chases a pointer per interned node where a `String` compare runs over contiguous bytes, while
the conjecture sort's pairs often share their left side, which `show_cmp` answers at once by identity. The sorts' 12.56
points left (the seeds sort 0.43 of them) are what S3 would replace with a minimum per group. Shares: the filter 37.3%
inclusive (35.6 before), `pool_conjectures` 31.2 (33.3), `verdict` 14.8 (14.3), `Term::show` 2.8 (13.0; `shuffled`
2.35 and the pin test's digest 0.45, S2's), `shuffled` 6.6 (6.2), `Plan::new` 1.4 (1.4), `mi_arena_try_purge` 2.7 self
(2.6).

*S2 landed (2026-10-29).* `Term::show_into` is public and writes through `fmt::Write`; `search::Fnv`, an FNV-1a 64
`fmt::Write` with `Fnv::of(|h| ...)`, takes the three hand-rolled FNV folds: `shuffled`'s hash of `{salt}|{lhs} = {rhs}`,
the pin test's digest, and `classes::text_hash` (which joins its trimmed lines by `\n` without building the join). No
text is built for any of them; `show` is `show_into` on a `String`. The test `shuffled_orders_by_the_fnv_of_the_law_text`
(`Fnv` of `"a"` and of pieces against FNV-1a's value for the whole; `shuffled` at salts 1, 2 and 7 over laws on every
term to size 3 against the same sort keyed by the text) failed to build before the change. The church_bv suite passed
(166 tests, 30 ignored; run `2026-10-29-s2-suite`) and both sequences stay pinned, the pin run's lines equal S1's once
sorted (run `2026-10-29-s2-pin`). Counts against `b9fe5a3` (runs `2026-10-29-s2-icount-*` and `-s2b-icount-L1`;
`docs/runs/2026-10-29/rows/2026-10-29-s2-icount.txt`): -2.2% at the best runs of the quiet pair (191.66 G against
195.89; 6-7% load) and -1.7% against a second quiet L round (195.05), every F run below every L run; a second pair at
27-33% load, from a game another user process had started, counted F2 2.0% above L2 and is not used (counts rise with
load, the purge being time-based), and the batch meant to repeat the pair stopped when the load gate (under 15%)
stayed shut for 30 minutes. So F has one quiet round, not the two the other items had; its direction and size are
beyond the noise of the quiet rounds (0.25-0.40% spreads) but not repeated. The profile after it (run
`2026-10-29-s2-prof`, `docs/runs/2026-10-29/rows/2026-10-29-s2-prof.txt`; untimed, 9% load against 17%) shows the time
saving: `shuffled` 1.63% inclusive (6.64 before), `Term::show` 0.03 (2.83); what remains of `shuffled` is the walk
(`show_into` 1.45 under its closure) and the hash (`write_str` 0.77), and the digest's `show_into` 0.29 (0.45). The
time share fell by 5.0 points where the count fell by 2.2% and the survey expected about 2: the `String`s' cost was
allocation stalls (`mimalloc`, 2.02 of `shuffled`'s 3.58 in the survey) more than instructions, as it read. Absolute
busy-sample totals are not comparable between profiles at different loads (50,071 against 49,229 here; 53,184 at 6%
load against 48,235 at 18% across F1, whose count fell 17%): shares within a profile are what is read. The sorts that
remain are `stream_laws`' 9.95 and `pool_conjectures`' 3.03 (union 14.63 with `shuffled`'s 1.63). `mi_arena_try_purge`
1.5 self (2.7).

*S3 landed (2026-10-29), in three commits.* Step 0 (`8f7c2bb`) pinned what the two salt-1 sequences did not cover,
before any ordering code changed: `stream_sequences_are_pinned_at_salt_0` (2 growths 58440 laws, digest
`0x4a7dc2260672672b`; 4 growths 230399, `0x8966904d38acdd30`; salt 0 is what a bare `loop_stream` or `rule_miner` run
gets with `RULEMINER_SHUFFLE` unset) and `small_streams_are_pinned` (six small streams at salts 0, 1 and `HELD_SALT`).
S3b (`db1e4e2`): `stream_laws` keeps its pool in growth order as `(level, term)` and `pool_conjectures` takes a group's
head as its least member by `(rank, show_cmp)`, whatever order the pool arrives in (test
`pool_conjecture_heads_are_the_least_whatever_the_pool_order`: reversed and rotated pools), so the pool sort is gone;
the seeds sort stays, because `c.reps()` comes in hash-map order and the growth's draw counter depends on the base
order. S3a: the conjecture sort and `pool_conjectures`' `cap` are gone (the contract is now an unordered set; the one
caller that sampled by stride, `laws_survive_a_law_file`, does it inline), and `shuffled` is a total order: the `Fnv` of
`{salt}|{lhs} = {rhs}`, then the text of both sides by `show_cmp`, with no hash at salt 0, so the conjectures are
ordered once and owe nothing to the order they arrive in (the tests `shuffle_is_a_fixed_permutation` and
`shuffled_orders_by_the_fnv_of_the_law_text`, which also cover salt 0 and a reversed input). Both salt-1 and both salt-0
sequences stayed byte-identical at each step, `small_streams_are_pinned` too, and at the last step `regenerate_held`
rewrote the four `held_*.txt` files unchanged (runs `2026-10-29-s3b-pin`, `-s3b-pin0`, `-s3c-pin`, `-s3c-pin0`, `-s3c-held`; the church_bv
suite passed, 168 tests and 31 ignored, runs `-s3b-suite` and `-s3c-suite`). Counts: S3b against `8f7c2bb` -9.4% at the
best runs and -9.5% at the medians (179.46 G against 198.13 G; six runs each, every F run below every L run; loads 12-26%;
`docs/runs/2026-10-29/rows/2026-10-29-s3b-icount.txt`), S3a against `db1e4e2` -4.6% and -5.3% (170.43 G against 178.72 G;
six valid runs each, F's 170.43-175.93 below L's 178.72-186.32; `-s3c-icount.txt`; two of its four L rounds failed, one
with a truncated trace and one with the disk full, so L is two rounds, 18% and 2% load). The two are separate A/Bs on
separate days' loads, so their product, 0.864, is not a measured pair. Profiles (`-s3b-prof`, `-s3c-prof`): the sorts'
union of busy samples 14.63 (S2) -> 5.71 -> 0.63, what is left being the seeds sort (0.51) and the sort over `u64`
keys inside `shuffled` (0.11, of its 1.94 with the hash and the walk); `show_cmp` 3.75 -> 0.71; busy samples 50,071 ->
43,064 -> 42,266 at 9%, 17% and 12% load. The counts fell by more than the sorts' share of busy samples (S3b: 9.4%
against the pool sort's 8.85 points; S3a: 4.6% against the conjecture sort's 3.0-3.4), the survey having put S1 and S3
together at no more than the sorts' 12.24 points; a reading, not checked: the sort's instructions are denser than its
share of time. One thing to watch, not a finding: `fill_op`'s inclusive samples rose across the three profiles (6,935,
7,489 and 7,806 of the busy samples), which may be the `ValueMemo` filling in growth order instead of text order (cache
locality) or the three loads; the instruction counts cannot show it, and the profiles are untimed, so a timed A/B
(`run.ps1 -Timed`) would be the check if the S3 time saving ever matters.

*F2 landed (2026-10-30).* `Classes::normalize` returns a `Term` (its `NormalForms` is a `HashMap<Term, Term>`) and takes
`&Job`: the filter reads only the normal form, and the production rewriter takes `step`, not `normalize`, so the plans
`normalize` built (`Cong` per changed node, `Trans` per replacement, the memo's `Rc`s) had no reader. `step` and
`normalize` share a plan-free `Classes::replacement` (the representative, the width and variable checks, the `VERDICTS`
lookup or build); `step` keeps the `table_steps` insert and `Plan::law`. Two changes beyond the survey's counting mode,
which it subsumes: `normalize` counts no step in `table_steps` (the filter's job is a throwaway, and the F1 survey bullet
found no `steps_if_closed` around `normalize`; every non-test caller is that filter), and `VERDICTS` holds `Arc<Verdict>`, so a hit copies no argument `Vec`. The
test `counting_and_compiling_agree` now checks `step` under counting rules (the same representative, the shared
`Plan::Counting`) and that `normalize` counts nothing; `normal_forms_are_memoized_per_operator_node` plants an entry in
the memo and checks it comes back, instead of `Rc::ptr_eq` on a plan. The church_bv suite passed (168 tests, 31
ignored; run `2026-10-29-f2-suite`), both salt-1 sequences and the salt-0 pair stay pinned (runs `2026-10-29-f2-pin`,
`-f2-pin0`) and `regenerate_held` left `held_*.txt` identical (`-f2-held`). Counts against `89e7fe0` in one batch (runs
`2026-10-30-f2-icount-{L1,F1,F2,L2}`; `docs/runs/2026-10-30/rows/2026-10-30-f2-icount.txt`): -2.4% at the best runs
(168.19 G against 172.30) and -2.9% at the pooled medians (169.76 against 174.75). The arms overlap, unlike S3's: 5 of
the 36 F-L pairs have F above L, so the direction holds and the size is a few percent, the survey's 1.8 points at most
plus the memo's drops. The profile after it (run `2026-10-30-f2-prof`, `docs/runs/2026-10-30/rows/2026-10-30-f2-prof.txt`;
untimed: 42,500 busy samples against 42,266): the filter 35.3% inclusive (39.4), `normalize` 30.9 (33.1); the work on
every visit 9.36 (12.69), with plans built 0 (1.50), lookup hits 3.37 (3.84), the walk and the rest 5.71 (7.29), the
closure's drops 0.28; first asks 21.56 (20.44), work F2 does not touch, whose samples rose 6% at the same busy total.

*Ord landed (2026-10-30).* `Term`'s `Ord` is the order of its `show()` text, compared without building it (the first differing head in
preorder decides by its token; a variable past `VARS` sorts after `z`, by index, since `show` cannot print it), and
`show_cmp` and the structural `Ord` are gone: S1's comparator became the one order. Commit one (`54302c7`) swapped it
and its callers; commit two converted the string-keyed sites to terms: `run_order` (rule table and miner ranking),
the miner's candidate sort, `twin_key` (now `Option<(Term, Term)>`, the least pair under the order) and the driver's
filter set, and the classes test's pair sort. The `show`-based oracles stay. Both commits kept the suite (167 passed,
31 ignored), the four pins, `held_*.txt` and the gate (rules same in 3 of 3 loops, M 145, held 1774, equal work) as they
were (runs `2026-10-30-ord-*`, `-ord2-*`). It is not a speedup: counts on the stream pin are +0.18% for commit one and
+0.087% for commit two (`docs/runs/2026-10-30/rows/2026-10-30-ord1-icount.txt`, `-ord2-icount.txt`), the price of a
tuple-token compare and uncached sort keys; the gain is one order, no strings in the sorts and `show_cmp`'s test and
buffers deleted. The miner's sorts have no count: the one miner test tried is 26 M, start-up sized. No profile was
taken after it (the change is under 0.2% and nothing in the cleanup queue depends on the shares).

*P1 landed (2026-10-30).* `Setup::process` sets mimalloc's `purge_delay` (option 15) to -1 on first use unless `MIMALLOC_PURGE_DELAY` is
set, in the harness for every church_bv process (a compile-time define does not exist for it in v3, unlike the large-page and
arena options in `.cargo/config.toml`); `machine::mimalloc_defaults_to_no_purge` failed at 1000 first. The suite (168), the
four pins and `held_*.txt` stayed as they were. The size is not re-measured: the count A/B reads +0.3% (best of 3; purge cost is
kernel time, not instructions), and the gate's job CPU swings 4% with arm order, more than the 7% it would have to show
(`docs/runs/2026-10-30/rows/2026-10-30-p1land.txt`).

*P1 timed again (2026-10-30, the landed build).* The same pin on CPU 8 with three arms (A commit two, B the P1 build, A2
commit two with the env var), `run.ps1 -Timed` run `2026-10-30-p1-time2`
(`docs/runs/2026-10-30/rows/2026-10-30-p1time-land.txt`). It ended at its 1 h cap with 3 clean rounds of 8 (the machine
was shared; round 3 ran at 18% other load, 29 s a run against 22). Job CPU medians: A 22.64 s, B 22.58, A2 22.45. **The
env var shows no effect on this base**: A2 - A is +0.08 s (-0.19, +0.08, +0.53 by round), wall +0.07 s, where
"P1 timed" read -1.90 s (-7.3%) in 8 of 8 rounds. B - A is +0.30 s (-0.06, +0.64, +0.30), inside the spread of the
A/A-sized differences here (about ±0.5 s), so landed and env var agree with each other and with zero. Peak process memory
is 2562 MB in all 9 runs (2564-2568 before). So the in-code set is equivalent to the env var, and neither shows a saving
now. Unexplained: why -7.3% became 0 between the F2 build and this one (the default arm's job CPU went from 26 to 22 s with the
`Term`-order commits in between, or machine state); with 3 clean rounds the null itself is thin. Falsifier: rerun the three arms on the
F2 exe (`2026-10-30-purge-time3`'s build), where the saving was seen, on a quiet machine; if it returns there, the
purge cost moved with the allocation pattern, not with the machine.

*cargo-mutants spike (2026-10-30, test-suite trimming survey).* cargo-mutants 27.1.0 on `src/kernel/spaces.rs` (112 mutants),
one shard of 20 (6 mutants), `-- --lib` as the test command, `--jobs 1`, pinned to CFF at BelowNormal (run
`2026-10-30-mutants-spaces-probe`, exit 3 = timeouts). Baseline 209 s build + 26 s lib tests. 6 mutants took 14 min: 3 caught,
1 unviable, 2 timeouts (`INDEX_MASK`'s `- 1` mutated to `+ 1` or `/ 1`, `spaces.rs:24`; each cost the auto-set 131 s
timeout), 0 missed. A rebuild is 31-37 s per mutant, so the whole module is roughly 2.5 h at `--jobs 1` (an extrapolation from
6 mutants, not measured). Feasible for one module as a before/after check on a trim, not for the whole crate; `--in-diff`
cannot drive it for a test-only diff.

*Alternatives to cargo-mutants (2026-10-30; survey, sources re-fetched by a verifier).* The only live Rust alternative is
mutest-rs (zalanlevai; nightly, mutants swapped at runtime from one build, 18 operators, last commit 2026-10-08, a research
tool): its claimed ~100x speed-up over cargo-mutants is not in the sources opened (the ICST 2026 abstract says only
"efficient"). mutagen (last commit 2022-07), Mull (C/C++, no Windows lock files), universalmutator (one rebuild per mutant),
cargo-mutamancer (v0.1, no mutants yet) and unclebob/mutator (`cargo test` per mutant) are not replacements. Cheaper
cargo-mutants runs: a 5% sample after operator selection took 6.54% of the time (Zhang, ASE 2013), `--shard` (each shard
repeats the build and baseline), `-- --all-targets` to skip doctests, a `mutants` profile with debug off.
*mutest-rs on this machine:* built and installed under the pinned `nightly-2026-07-18` into `%LOCALAPPDATA%\mutest-rs\inst`
(run `2026-10-30-mutest-build`, exit 0); `cargo mutest run -p tatic --lib --filter-mutations file:src/kernel/spaces.rs`
(run `2026-10-30-mutest-spaces`) panics in `mutest-driver\src\main.rs:87`, "cannot find target in Cargo package
metadata". Inference, untested: the driver canonicalizes rustc's input path (`src\lib.rs`, giving a `\\?\C:\...` path on
Windows) and compares it with cargo metadata's `src_path`, so the match fails. The wrapper recorded exit 0 for that run
(cause not checked), so read the headline. Not patched: a fix is a change to
third-party code; the check is a one-line path normalization in `main.rs:85`, about 10 minutes to try.

*Cheaper than mutation (2026-10-30 survey; sources re-fetched by a verifier, the history-replay items unchecked).* Extreme
mutation (whole function bodies; Descartes) ran 13 min against 37 min for PIT's default mutators and 4 h for all of them on one
Java industrial suite, with 409 survivors to triage against 23,835; cargo-mutants already replaces function bodies. Google's
diff-scoped, covered-lines, one-per-line sampling cut the median from 820 to 77 to 7 mutants per change (a review signal, not a
score). A per-test coverage matrix shortlists duplicates only (equal coverage is not equal checking); its cost on Windows
(process-per-test spawn and Defender, or an in-process counter reset in a serial harness) has no published figure. Checked
coverage and assertion counts have conflicting evidence and no Rust tool. History replay is poor here: of 1369 commits, 110
subjects match fix/bug/wrong, 9 touch `src/` and `tests/` together, and the two checked do not revert cleanly (`git apply -R`
fails on `kernel.rs`, 131 and 126 later commits).

*Per-test coverage matrix spike (2026-10-30, run `2026-10-30-cov-spike-all2`, 168 non-ignored `church_bv` tests, debug build with `-C instrument-coverage`, one process per test).* Cost: 20 min wall at CPUs 0-7,10-11 (per test: run 5.0 s, `llvm-profdata merge` 0.44 s, `llvm-cov export` 1.02 s; instrumented build 2 min; about 3 GB of lcov, deleted). Result: no usable shortlist. Counting the harness files (`tests/church_bv/`) every test is unique, because each test body is its own covered lines; counting `src/` only, 131 tests cover 0 lines (they test the harness crate itself, which the filter drops) and form one "identical" group, 7871 strict subset pairs, 162 of 168 with no unique line. The two views bracket the answer: line coverage here either separates everything or merges everything, so it cannot name duplicates; only the six `src`-heavy groups (e.g. the 1090-line `rewrite_plan`/`encoding_search` group) are real candidates, and equal coverage is not equal checking. The sampled mutation run (below) is the check that can fail; the matrix is not worth repeating.

*Sampled mutation run (2026-10-30, run `2026-10-30-mutants-spaces-sample6b`).* 6 of the 112 `spaces.rs` mutants (5.4%), picked by a Fisher-Yates shuffle from an LCG seeded 20261030 over `cargo mutants --list --no-shuffle`, run with `-F` per name, `--jobs 1`, `-- --lib`, CFF at BelowNormal. 11 min (279 s build + 29 s tests baseline, about 55 s per mutant): 4 caught, 2 missed, 0 timeouts: `reset_vec` `/` to `%` (`spaces.rs:92:28`) and `Spaces::resolve` `-` to `+` (`:269:26`) survive the lib tests. So this crate-level suite does not pin those two lines (the fixed 1/20 shard was 3 caught, 1 unviable, 2 timeouts, 0 missed): a trim judged by this sample would have a baseline of 4 of 6 caught, and any run that drops below it fails. Six mutants give a rough rate only (4/6 caught; a 95% interval is wide); the two survivors are the useful part, as named gaps.

Both survivors were closed the same day (run `2026-10-30-mutants-spaces-rerun2`, 2 of 2 caught): `resolve`'s `-` was equivalent to `+` while `w` was 0 (every test opened its region on an empty persistent space), and `reset_vec` had no test that a small region after a large one gives the capacity back. Two tests in `spaces.rs`; the suite was not otherwise changed.

*Why `church_bv` is slow in a plain `cargo test` (2026-10-30, profile in `%LOCALAPPDATA%claude-runs	atic6-10-30-q1prof`, shares only, machine at 40-60% load).* `search::a_stream_sequence_is_the_same_on_any_thread_count` took 166 s with `small_streams_are_pinned` (two builds of 56 streams: 4 threads 67.7 s, 1 thread 72.9 s; the four threads' CPU summed to 180 s against 73 s serial, the first build filling the shared memos cold). Shrinking its budget (2000 to 500, 2 to 1 growth) cut it only to 87 and 72 s, a fixed cost per build. The profile puts 62-78% inclusive in `stream_laws` -> `ValueMemo::fill` / `fill_op`, and the top self frames are unoptimized `Zip::next` and `__iterator_get_unchecked` slice-iterator adapters: the debug (`opt-level` 0) test profile. The same two tests with `CARGO_PROFILE_TEST_OPT_LEVEL=1` and `CARGO_PROFILE_DEV_OPT_LEVEL=1` (debug assertions and `check_replay` still on) took 19 s, 8.7x less (4 threads 7.2 s, 1 thread 9.6 s); one run, loaded machine, cold 10 min build in a separate target dir, so the rebuild cost of an edit at that level is not yet measured.

*Opt-level 0 against 1, whole suites (2026-10-30, run `2026-10-30-opt-level-ab`, `--test-threads 8`, CFF, not timed-gated: machine load 77% for the opt 0 arm and 31% for opt 1, so the ratios are rough, but they are far larger than the load difference).* `cargo test --lib`: 32.5 s against 2.9 s (11x). `church_bv` (168 tests): 157.9 s against 12.0 s (13x). Rebuild after a one-line edit of `src/kernel/spaces.rs`: lib 7.9 and 9.0 s against 4.3 and 4.6 s; `church_bv` 11.1 and 12.6 s against 6.0 and 6.0 s, so opt-level 1 was also faster to rebuild (incremental codegen has less to unwind; a clean build was about 10 min in the separate dir, not measured against opt 0). One lib test failed in the opt 0 arm's first run under that load (359 passed, 1 failed; its name was not captured) and passed in two reruns at load 40%: a load-sensitive test. Identified 2026-10-30 (runs `2026-10-30-flaky-lib-load`, 10 of 10 pass at 24% load, and `2026-10-30-flaky-lib-2cpu`, the lib suite pinned to 2 CPUs with 12 test threads at opt-level 0): 6 of 12 runs failed, each with 1 or 2 of `kernel::tests::def_eq_is_linear_on_a_chain_that_differs_at_the_bottom`, `infer_types_an_application_spine_at_once` and `infer_memo_skips_unused_inner_binders`. All three go through `assert_scales` (`src/kernel/tests.rs`, a ratio of two wall-clock runs, 3 tries), which contention breaks when the short and long runs are slowed unequally. Not fixed: a count of work done would replace the clock, but that is a change to the kernel tests.

*Workspace at opt-level 1, dependencies at 0 (2026-10-30, run `2026-10-30-opt-level-split`, load 24%, `--config profile.{test,dev}.package.tatic.opt-level=1`, own target dir).* Cold `--no-run` build 160 s (the all-opt-1 cold build above was about 9.5 min with its 19 s test run, so the dependencies, wasmtime among them, are most of a cold build). `--lib` 9.2 s (opt 0: 32.5 s, all opt 1: 2.9 s); `church_bv` 30.8 s (158 s, 12.0 s); rebuild after a one-line edit: lib 10.4 and 24.3 s, `church_bv` 33.4 and 26.8 s (all opt 1: 4.3-4.6 and 6.0 s; the rebuild gap is not explained). So the dependencies at opt 0 cost 3x on the suites: hot generics (hashbrown, iterator adapters) are instantiated from them, and the workspace-only setting is not enough.

*An always-on kernel work counter replaces the wall-clock ratio in `assert_scales` (2026-10-30; run `2026-10-30-flaky-lib-2cpu-work`; instruction counts by `icount.ps1`, CPU 4, 3 runs each, not through the wrapper).* `Spaces` has a `work: Cell<u64>` that an inlined `s.tick()` bumps once per call of the six recursive workers (`shift_unchecked`, `inst_rec`, `whnf_step`, `nf_whnf`, `conv_whnf`, `infer_node`); `kernel::work()` reads this thread's total and a caller takes a difference. A memo hit counts nothing and `infer_node` runs only on a type-cache miss, so the count is the work done. Cost, release `church_bv` on four proof tests: 5,556,790,547 instructions without it, 5,550,064,702 with it (best of 3; median over best 0.05% for both, max over best 0.67% and 0.18%), so under the 1% bar and not measurable. `work_is_deterministic_and_scales_with_the_query` pins that two runs of a query from a fresh thread count the same. Eight of the ten `assert_scales` callers now pass `worked(..)`, the change in `work()`; `brief` and `close` run code the six workers don't see and stay `timed(..)`. The ratios are exact: def_eq on chains 3,004 to 48,004 (16x for 16x the size; limit then 80x), infer on a spine 1,504 to 24,004, stuck spine 7,023 to 112,023, infer under unused binders 510 to 4,010, infer on a DAG 14 to 24 (limit then 8x; a tree walk of the 2^20 shared terms would be about 1000x); subst_top 3 to 3, def_eq shared domains 19 to 19 and def_eq equal sides 0 to 0 (nothing normalised). The limits of the eight are now about 1.5 times the linear ratio (24x for 16x the size, 12x for 8x, 3x for the DAG, 2x for the three constant ones; they were 80x, 30x, 8x and 4x), so a quadratic regression (256x, 64x) fails with a wide margin and 2x extra work does not pass. Pinned to 2 CPUs with 12 test threads at opt-level 0, the setup that failed 6 of 12 runs above, the lib suite passed 12 of 12 (361 passed each, 44 to 71 s). Uses beyond tests (a deterministic cost signal for the model) are not built.

*Work in place of M, replayed (spike, 2026-10-30, runs `2026-10-30-work-vs-m-spike2` and `-spike3`, release `church_bv` at 0cf04c6 plus a throwaway ignored test, since reverted, that wrote per law the change in `kernel::work()` while building and while checking, with the machine fallbacks M counts; CFF, not timed-gated, one run per cell).* The 2026-10-10 windows no longer exist (the streams were rebuilt, and the class table now closes the old kind of law). On the 539 laws of two recent serve windows (sbo3 skip 0-200, cmp3d, the 2026-10-17 `join-trace2` runs) M is 0 with and without a library, and `steps` is 0: nothing for M or a library to grade, while work still spreads (p10 1.2k, median 6-15k, p90 47k-97k, max 107k-237k per law). On the first 300 laws of the held bands (`held_13`, `held_17`, which the class table does not close) with no library against the 33-rule cmp3d library (another family's, so a weak library): M falls 58 to 49 (band 13) and 89 to 82 (band 17), while kernel work stays flat: building 21.0M to 20.6M and 45.7M to 47.8M, checking 0.68M to 0.71M and 0.89M to 0.95M (the proofs of the lemmas are checked once, during the build, so the check is the small part now). So, as on 10-10, a library moves M and not the kernel's work. Per law, Spearman rho of total work (build and check) against total wall time is 0.96-0.98 on both bands (0.88-0.96 on the null windows); rho of fallbacks against check time is about 0 (-0.02 to 0.12); 202 of 213 and 166 of 179 machine-free laws cost more work than the cheapest machine-proved law, so M's classes overlap fully. Where work does not follow time: build wall time falls with the library (19.9 s to 11.2 s, 37.5 s to 26.1 s) while build work does not, because `work()` counts only the six kernel workers and not the rewrite search that a library shortens. So work is a better grade than M for the kernel's cost, it is a deterministic proxy for time at rho 0.96-0.98, and it misses the search cost; a reward from it needs a term for that. With libraries mined on the current streams instead (run `2026-10-30-work-vs-m-spike4`, the 50- and 73-rule `2026-10-23-cold-streams` libraries, same 300 laws per band): M 58 to 33 and 39 on band 13, 89 to 77 and 79 on band 17; build work rises, 21.0M to 24.6M and 22.3M, and 45.7M to 52.3M and 47.3M; build wall time falls, 19.9 s to 11.6 s and 8.4 s, and 37.5 s to 21.3 s (the 73-rule cell on band 17 read 50.5 s build and 1.8 s check, a load spike that was not checked, so ignore it). So the gap is confirmed with a library for the stream: it cuts M and the search time and does not cut kernel work, which a reward from `work()` alone would not credit. Rule steps do not stand in for the search: 75 to 399 steps in total per arm, rho(steps, time) 0.19-0.40, and adding them to work does not raise the fit. Cost of a search tick (prototype, since reverted: a counter in `RewriteState` bumped once per `rule_step` call and once per candidate rule tried, the hottest rewriter loop; instruction counts of the 4-proof-test workload as above, 3 runs, CPU 4): 5,560,054,185 with it against 5,550,064,702 (+0.18%) and 5,574,854,838 (-0.27%) for two runs of the same baseline exe, the second at machine load 100% (one prototype run read 6.02 G, +8%, load, dropped). So the tick costs less than the 0.3% the baseline itself moves between runs. **It does not track the search time (negative, same day, run `2026-10-30-work-vs-m-spike5`, reverted, no patch kept).** Built as a `Job.search` counter (not in `RewriteState`, which `proving` swaps out) read through `Spent.search`, with a test that it repeats and grows with the term, it counted only 1k to 4k ticks per 270 laws on the held bands against 21-48M of kernel work, and per law rho(search, time) was 0.26-0.33 and adding it to work did not move rho(work, time) (0.93-0.97). With the 73-rule library the count rose (1k to 3k on band 13, 2k to 4k on band 17) while the time fell (band 17: 36.8 s to 24.3 s in this run; band 13 read 13.1 s to 14.5 s here against 19.9 s to 8.4 s above, so the wall times move with load). The laws are mostly closed by the class table and the join before `rule_step` is asked, so `rule_step` is not where the search time goes; the table steps, the join and the plan building are not counted. The profile that follows shows it is not the table or the join either.

*Where a held-band build's time goes (samply, 2026-10-30, run `2026-10-30-build-prof-h17b`; debug-info build of the spike test, band 17's 268 laws, no library and the 73-rule library, one thread each, 69,327 and 50,880 samples, load 65%, so shares only).* **Kernel inference is about 95% of it; the search the rewriter does is 3-4%, so the inference above was wrong.** `law_proof` (the proof builder) is 58.5% inclusive without the library and 67.2% with it, and the rest is mostly the kernel check of the finished proof, which `stacker` runs on grown stack segments, so its frames lose their parents: of the samples outside the loop's closure, 99% are kernel `check`/`infer`. `rewrite_plan` is 4.4% (3.1% with the library) and that includes `Classes::build` at 4.1% (2.7%); the join is 0.2%, `prove_rule` 0.3%, and `rule_step` does not show (inlined, under 0.1%). So no search tick, in `rule_step` or the class table or the join, can explain a library's saved time. The library's samples fall 18.4k (27%) while `work()` rises 4%, and the drop sits in term-space growth (`Space::push` 15.9k to 7.6k samples, `finish_grow` 9.8k to 3.5k, `ntoskrnl` self 12.1k to 5.3k, a split that is unreliable here). **A space counter does not explain it (spike, same day, runs `2026-10-30-space-growth-spike` and `-abab`, reverted).** Counting nodes pushed, node-vec reallocations and elements copied, table growths and shrinks per law on bands 13 and 17: nodes pushed is 0.41-0.47 of `work()` in every group and tracks time as `work()` does (rho 0.92-0.96, so it adds nothing); reallocations and shrinks are under 500 per band (a region is small); copy volume is equal between arms (78.6M elements on band 17 in both) and has rho 0.26-0.34 with time. Fitting time on `work()` plus any of these on the no-library arm predicts the library arm at 29-30 s on band 17 against 20.5 s measured. The per-work cost falls evenly, 35% for laws with and without a machine fallback, while pushes per work stay level, so it is not a count of anything the space does. The size of the drop was partly load: the runs above went no-library first, and an interleaved ABAB on band 17 (library, none, library, none) gave 26.8, 28.8, 25.9 and 33.3 s, so 545 against 667 us per 1000 work units (-18%), with 15% spread between the two no-library runs; the earlier 36.8 s to 24.3 s (-34%) overstated it. Not explained: the remaining 10-20% per-work gap (a smaller working set with the library's plans is a guess; it would need cache-miss counters, which this machine's xperf setup does not collect for one thread). So no counter beside `work()` is justified by this: it already ranks laws by time at 0.93-0.97, and a library moves time per work unit by at most 10-20%, which it also moves by 15% between two runs of the same arm.

