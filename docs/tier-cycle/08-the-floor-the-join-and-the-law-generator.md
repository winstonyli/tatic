## The floor, the join and the law generator

### The floor and the bounded join (2026-10-17)

*What the floor is (2026-10-17).* At dose `all`, the mined batches leave 171 laws that need a whole-term machine proof
(none unproved): 92 distinct for cmp3d, 37 for add3 and 10 for sbo3. With each loop's final library (after its second
mine, which saw batch 1) 124 still do (cmp3d 94, add3 18, sbo3 12). Mining on exactly those laws, with that library
as the base (`rows/floor/insample.sh`), adds 15 rules for cmp3d, 1 for add3 and none for sbo3, and leaves 101 (72, 17, 12).
Mining on the laws themselves does not remove them, so no choice of laws to mine on will. A throwaway diagnostic
(`patches/floor_diag_probe.patch`, `FLOOR_DIAG=1`) prints, per remaining law, the cycle cuts and both normal forms
(`rows/floor/diag.tsv`):
- **74 of the 101 look like permutations.** Both normal forms use the same multiset of symbols (`rows/floor/perm.awk`;
  the common shapes below are operand or variable permutations, checked by eye): add3 14 of 17,
  sbo3 12 of 12, cmp3d 48 of 72. add3 and sbo3 differ in which summand of x + y + z carries the + 1 (`sub(t, -1)`),
  e.g. `add(sub(add(x, y), -1), z)` against `add(sub(x, -1), add(y, z))`. cmp3d's include `lt(xor(a, -1), b)` against
  `lt(xor(b, -1), a)` (21 laws) and `lt(shl1(y, 0), add(sub(x, z), y))` against `lt(shl1(y, 0), add(sub(y, x), z))` (19).
- **61 hit a cycle cut while being proved:** every add3 and sbo3 law, and 32 of cmp3d's. The libraries hold rules that
  move operands around (add3's has both `add(sub(x, y), z) -> add(sub(z, y), x)` and `add(sub(x, -1), add(y, z)) ->
  add(sub(add(x, y), -1), z)`), and the cut leaves each side wherever its chain stopped. The exact cycles were not
  traced.
- **27 are not, all with a cycle cut:** 24 cmp3d `lt` laws and 3 add3 laws (e.g. `sub(-1, sub(xor(y, z), x))` against
  `sub(add(-1, x), xor(y, z))`). Several keep subterms unsimplified (`sub(t, 0)`), presumably frozen by the cut, and a few
  are `lt` facts about wraparound, e.g. `lt(t, sub(0, z))` against `lt(t, add(sub(t, 0), z))`.

So the floor is not about rule size, and target (a) as worded (laws beyond 5 nodes) would not lift it. A rule that joins
two permutations of a term is itself permutative: plain rewriting either cycles on it (the cut) or must leave one
orientation out. A larger pool would add more such rules, not orient them; that is reasoning, not tested. The general
mechanism for permutative rules is ordered rewriting. `rule_step` already applies it per permutative rule, by `show()`
order; one order for every instance was `PERM_ORDER=lpo`, deleted as negative on 2026-10-11 ("Cycle cut; lpo and a
cycling penalty are negative results"). It was rechecked against the floor below, and is negative again.

*Ordered rewriting against the floor (negative, 2026-10-17).* `patches/floor_lpo_probe.patch` ports the deleted path order
(`lpo_greater`) to the current `Term`. `FLOOR_LPO=tied` checks every weight-tied mined rule instance against it (the old
`PERM_ORDER=lpo`); `FLOOR_LPO=all` checks every mined rule instance. M at dose `all` (`rows/floor/lpo.sh`):

| | none | tied | all |
|---|---|---|---|
| the 101 floor laws, in-sample libraries | 101 | 108 | 105 |
| mined batches (1327 laws), each loop's library | 145 | 2925 | 3845 |

- **With libraries mined under the order, more of the floor goes.** Mining in-sample on the floor laws under
  `FLOOR_LPO=all`, starting from each loop's library, leaves 63 of 107 (`insample_lpo.tsv`), against 101 of 124 without it.
  The order lets new rules join permutations that otherwise cycle.
- **The whole loop pays far more than that.** Cold sweeps with every mine and serve under `FLOOR_LPO=all` (salts 1, 2):
  mined-batch M 264 / 282 plain against 120 / 128 now, and 143 / 167 at dose `all` against 14 / 22 (`lpo_<0|all>_s<salt>.tsv`).
  Libraries that fire freely and get cut cover far more laws than libraries held to one order. This agrees with
  2026-10-11. Ordered rewriting is not the lever; joining the permutations without that cost would take completion
  (adding the critical-pair rules that make the ordered system confluent); see the next paragraph.

*Completion on the floor: cmp3d's floor joins, add3's and sbo3's are one rewrite cycle (2026-10-17).* The cheapest
completion step, in-sample: to each floor law's in-sample library (`rows/floor/insample.sh`'s working libraries) add every
remaining floor law's own normal-form pair as a rule, oriented forwards (left normal form to right), backwards, or from
the larger `show()` to the smaller, then serve the floor laws and the loop's mined batches again (`rows/floor/complete.sh`,
code at 9c601c3 with the oracle-headroom probe built in but none of its variables set; `complete_<fwd|back|down>.txt`):

| orientation | cmp3d floor | add3 floor | sbo3 floor | cmp3d batches | add3 batches | sbo3 batches |
|---|---|---|---|---|---|---|
| none (in-sample library) | 72 | 17 | 12 | 133 | 21 | 14 |
| forwards | 43 | 17 | 12 | 104 | 21 | 14 |
| backwards | 32 | 17 | 12 | 93 | 21 | 14 |
| larger to smaller | 30 | 17 | 12 | 91 | 21 | 14 |

- **cmp3d's floor partly joins, and the joining transfers.** The added rules remove up to 42 of cmp3d's 72 floor laws and
  42 more machine proofs on its mined batches (133 to 91), with no orientation making anything worse.
- **add3's and sbo3's do not move at all, in any orientation.** For 26 of their 29 laws the two sides already sit in one
  rewrite cycle, and the cycle cut leaves each side at a different member of it (next bullet). Traced on one add3 law (`NF_TRACE=1 search::normal_forms`):
  `add(add(x, y), sub(z, -1)) = sub(add(x, y), sub(-1, z))` cycles through `sub(add(x, y), z) -> add(sub(x, z), y)`,
  the built-in AC, and `add(sub(x, -1), add(y, z)) -> add(sub(add(x, y), -1), z)`; one side stops at
  `add(sub(add(x, y), -1), z)`, the other at `add(sub(x, -1), add(y, z))`, both members of the same cycle.
- **Most of the floor is that case.** Tracing each side of every floor law alone (`rows/floor/samecycle.sh`), one side's
  normal form is among the terms the other side's rewriting visited for add3 14 of 17, sbo3 12 of 12 and cmp3d 33 of 72:
  59 of 101 (`samecycle.txt`). These laws are joinable already; the cut just stops the two sides at different points.

The general fix this points to is in the cycle cut, not in the rules: on a cut, return a canonical member of the cycle
(e.g. the `show()`-least term visited) instead of the term where the cut fired. Rewriting is deterministic, so two sides
that reach the same cycle would then get the same normal form. It needs a proof from the entry point to that member.
`REWRITE_PATH` holds only the terms; the plans between them are composed up the call stack as the calls return, so the
choice would have to be made in the call that pushed the cut's path entry (`CUT_LOW` already records which one), and the
memo's replay rules (`rewrite_memo`) would have to respect it. Not built, and not designed further. If it works, it
might also make the per-rule `show()` order in `rule_step_in` unnecessary, and it needs no order on whole terms, which is
what made `FLOOR_LPO` costly. Why the added rules leave add3 and sbo3 unchanged was not traced with them in; the trace above
is with the in-sample library alone.

*What kind of new law pays most (2026-10-17).* `patches/law_bucket_probe.patch` (a superset of the oracle-headroom probe)
takes the twin-free extras from one bucket, by skeleton (the law with every variable written `v`, smaller side first):
`past` (skeleton among the laws the mine is mining on), `future` (not past, but among phases 1-3's laws: peeks),
`novel` (neither), `unseen` (not past; legitimate) and `random` (no skeleton filter; despite the name, the first
twin-free laws in stream order, as in the earlier arms). Counts are matched to what
the smallest bucket offers: add3 60, sbo3 180, cmp3d 350 per mine (`MINE_EXTRA=add3:60,sbo3:180,cmp3d:350`). Every
bucket filled except novel (add3 3042 and cmp3d 20286 of 3600 and 21000 extras over the run) and past sbo3 (10797 of 10800).
Mined-batch M over salts 1-10 (`rows/oracle_headroom/bucket.sh`, `salts_b_<bucket>_s<salt>.tsv`):

| bucket | M | cmp3d | add3 | sbo3 | per salt |
|---|---|---|---|---|---|
| none (plain) | 1169 | 550 | 282 | 337 | 85-137 |
| past | 966 | 397 | 226 | 343 | 79-112 |
| novel | 951 | 452 | 221 | 278 | 73-122 |
| random | 624 | 253 | 148 | 223 | 50-74 |
| unseen | 581 | 247 | 130 | 204 | 45-73 |
| future | 578 | 248 | 139 | 191 | 41-73 |

- **The laws that pay share shapes with what comes next, but not with what is being mined.** More of the mined batch's
  own shapes gives -17%, and shapes the family never serves -19%; shapes the next batches have -51%.
- **The legitimate filter gets it without peeking.** `unseen` only drops the shapes being mined, and is as good as
  `future` (581 against 578), because the stream's shapes recur: at salt 1, 65-82% of each loop's `unseen` extras have a
  future skeleton (by overlap with the `future` arm's extras), the rest novel.
- So for a proposer: don't propose more of the shapes the miner already has; propose other shapes the family uses.
  Shapes from outside the family pay little. Caveat: the skeleton merges every renaming and operand placement of
  variables, so `past` also holds laws that differ from the mined ones only in where the variables sit.

*The twins gap: what anticipating the next laws' renaming classes is worth (2026-10-17).* At dose `all`, twin-free
extras leave M 405 and extras with twins 171. Per law of the mined batches (13270 over salts 1-10, all loops), whether
it needs a machine proof in the twin-free arm (`T`) and in the twins arm (`D`), and whether its renaming class (as in
`canon.awk`) is among the twins arm's extras (`rows/floor/gap.awk`, counts in `gap.txt`):

| | has a twin | no twin |
|---|---|---|
| machine in both | 58 | 19 |
| machine only twin-free (twins fix it) | 297 | 31 |
| machine only with twins (twins break it) | 58 | 36 |
| neither | 10357 | 2414 |

- **The gap is direct: the twins arm mines on the test laws themselves.** Twins fix 328 laws and break 94 (net 234 =
  405 - 171). 297 of the fixed laws have their own twin among the extras, and fixed laws with a twin outnumber broken ones
  5 to 1 (297 against 58); without a twin it is about even (31 against 36), so on laws without a twin the twins arm's libraries show no net gain.
  By family the net gain is cmp3d 65, add3 83, sbo3 86.
- **So anticipating the next laws' renaming classes is worth the whole gap, about 234 of 405, but only by predicting the
  test laws.** No proposer can do that for laws from outside it. In the real setting the stream is the proposer's own pool,
  so mining on the pool ahead of serving it is legitimate and reaches about 171: the loop then becomes one offline mine
  per family ("How many extra laws", last bullet). For laws from outside the pool, twin-free (about 400) is the honest
  floor for more laws.
- **Most of the twin-free 405 is coverage, not floor.** The same in-sample procedure on the twin-free arm's 405
  (`rows/floor/insample_t.sh`, 90 loops, 60 s): each loop's final library leaves 206, mining on exactly those laws leaves
  140 (cmp3d 108, add3 19, sbo3 13; `insample_t.tsv`), against 101 for the twins arm. Of the 140, 61 look like
  permutations (`perm.awk` on `diag_t.tsv`), 102 hit a cycle cut, and for 86 one side's rewriting visits the other side's
  normal form (`samecycle_t.txt`: add3 15, sbo3 12, cmp3d 59). So a cycle fix would reach the same share of either floor
  (61% here, 58% there); the remaining 265 of the 405 go once the miner sees the laws, which only laws from the pool give.

*Equational reach of the floor: every floor law joins within 5 steps (2026-10-17).* Neither church_bv nor the kernel has
a union-find or e-graph over terms (the kernel's `conv` keeps a per-call set of equal pairs; `typing.rs`'s union-find is
over types), so before choosing between a canonical cycle member and an e-graph, a bound on what any join mechanism could
reach: `patches/floor_bound_probe.patch` (`floor_equational_reach`) searches breadth-first from both normal forms of each
floor law at once, one equation step at a time at any position, using every built-in, promoted and library rule in both
directions (a direction only when it introduces no variable), plus commutativity of add, and, or, xor and their
associativity, with terms of at most the larger normal form's size plus 2 nodes and 50000 terms reached.

| floor | laws | joined | 1 step | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|---|
| twins arm, in-sample (`diag.tsv`) | 101 | 101 | 34 | 17 | 17 | 12 | 21 |
| twin-free arm, in-sample (`diag_t.tsv`) | 140 | 140 | 58 | 22 | 22 | 15 | 23 |

- **All of them join, and fast.** Every search took under 0.01 s (a search that fails takes up to 0.9 s). A control
  pairing each law's first normal form with the next law's second normal form in the same library (`bound_ctl_*.tsv`, 140
  pairs) joins exactly the 21 pairs that are equal on random inputs (neighbouring floor laws often share their normal
  forms, so these are floor pairs again) and none of the 119 unequal ones. Every rule is a proved law, so this checks the
  probe's code, not the rules.
- **Many are one rule application away.** 92 of the 241 normal forms differ by one equation step. The commonest is a
  cmp3d library rule `lt(x, sub(y, z)) -> lt(x, add(sub(x, y), z))` (50 laws, either direction): one side is the other's
  image under it, but rewriting that image cycles back, and the cut stops it. add3's `add(sub(add(x, y), -1), z) ->
  add(sub(x, -1), add(y, z))` closes 19 (the traced example above).
- **So the floor is a join problem, not a missing-rules problem.** The rules in force already prove every floor law;
  directed rewriting with a cycle cut just cannot find the proofs. This covers the 37 cmp3d permutation laws with no cycle
  cut too, which a canonical cycle member would not reach.

Every step the search takes is a proved rule, AC or commutativity, so a join gives a proof plan (`Plan::cong` around
`Plan::law`, `Plan::sym` for the reversed direction). The probe does not build those plans (built since: "The bounded
join removes the floor"). Rows: `rows/floor/bound_*.tsv` (family, library, steps or `none`, law, seconds, equal on random
inputs, the equation of a one-step join).

*The bounded join removes the floor (2026-10-17, 43c6d8f, cad853e, 8d5b29d).* `join_eq` (`crates/church-bv/src/rewrite.rs`)
is the probe's search building plans. Where `prove_eq` or the `lt` path of `rewrite_plan` would fall back to the whole-term
machine proof, it searches breadth-first from both normal forms at once over these steps:
- every rule in force (built-in, promoted, mined, not ablated, not being proved), in both directions where a direction
  introduces no variable and keeps `lt` at the root;
- associativity and commutativity of add, and, or, xor.

Terms stay within the larger side's size plus 2 nodes, and the search stops after `JOIN_VISIT` (1000) reached terms. A
path becomes `Plan::cong` around `Plan::law` (with `Plan::sym` for a reversed step), and a meeting at `u` gives
`trans(a = u, sym(b = u))`. Only pairs equal on 16 random inputs are searched. `ABLATE=join` turns it off. Test:
`join_eq_closes_an_equal_pair_by_rule_and_comm_steps`.

Full sweeps (`mines own cold pooled`), salts 1-10, with one exe on and off, the two arms of a salt side by side (run
`2026-10-17-join-final`; CPU 21% at launch, RTP off; rows in `docs/runs/2026-10-17/rows/join-final*`):

| total M, salts 1-10 | join off | join on |
|---|---|---|
| ref mines (40) | 160 | 2 |
| own loops (90) | 865 | 13 |
| pooled loops (90) | 757 | 33 |
| cold loops (90) | 4380 | 1568 |
| wall, 10 sweeps | 50 s | 88 s |

- **The floor is gone.** Own and pooled M fall 98% and 96% on every salt (per salt: own 0-4, pooled 0-9). The 10-salt
  cold-only run at cap 5000 (`2026-10-17-join-cold`) gave 1530 against 4380, -60% to -68% per salt.
- **What is left in cold loops is their first batch.** That batch accounts for 1443 of cold's 1568, served before any
  rule is mined, so the join has only the built-ins, promoted rules and AC (off: 3211). The later batches fall from
  851 and 318 to 87 and 38.
- **Sound.** With the join on, the ref mines (full serving check) built and kernel-checked all 10000 laws they served, 9998
  with no machine proof (join off: 9840). Each step is an instance of a proved rule or of an AC law.
- **Fewer rules are mined.** Rules at the end of the loops, summed: ref mines 612 to 423, own 2120 to 1278, cold 1554 to
  709, pooled 3919 to 3512. The miner's gain counts the laws a rule takes off the machine proof, and a joined law is
  already off it.
- **Cost: M no longer shows the search.** A joined law is free in M, but the search costs time: the sweeps' wall time
  went from 50 s to 88 s, and the ref mines' summed seconds from 6 to 29, all in cmp3d (`lt` laws) to the second.
  - A trace of the cmp3d mine and cold loops (salt 1, cap 5000, run `2026-10-17-join-trace`, patch
    `docs/runs/2026-10-17/patches/join_trace.patch`) counted about 48000 searches. Of the readable lines (63-70%; the
    threads' lines interleave), 3.5k searches failed (1.5k at the cap) and cost about as much CPU as the 30k that
    succeeded (74 s and 63 s).
  - The searches repeat: 908 distinct failing pairs and 2683 distinct joined pairs, each searched again under later rule
    sets. A success reaches a median of 28 terms (p90 727, p99 about 5000).
  - Indexing the steps by root operator, through the same `PatIndex` as `rule_step`'s rules (cad853e), took a reached
    term from 6.1 to 2.9 µs and the traced run from 69 s to 33 s, with M and rules unchanged.
- **Cap.** Run `2026-10-17-join-cap`, salts 1/2 (M as mines/own/cold/pooled, wall s):

  | cap | salt 1 | salt 2 |
  |---|---|---|
  | off | 23/74/451/58, 9 | 21/102/450/99, 8 |
  | 300 | 0/6/163/6, 12 | 1/2/158/4, 8 |
  | 1000 | 0/1/163/7, 14 | 0/0/161/2, 10 |
  | 5000 | 0/0/156/2, 47 | 0/0/152/0, 23 |

  1000 became the default (8d5b29d): 5000 leaves a few laws fewer for 2-3 times the time. Wall times here are side by
  side under 60% foreign CPU load, so they compare arms only within a salt.
- The kernel cost of joined proofs and the miner's view of the join: next section.

*The miner sees the join; a met join's plan survives rules added off its path (2026-10-17).*
Options, research and probes: `docs/decisions/2026-10-17-monotone-join.md`.
- **Blind spot.** The miner's gain bound asks which laws a candidate rule touches (`Trace::touched_by`), but a law's trace
  held only the rule steps of rewriting, not the terms its join examined. A candidate acting only inside a join looked
  harmless. Now a join adds the terms it examined, with their subterms, to the trace (`Fired::Join`); a candidate
  touches a join item by its left side, or by its right side where the join could use the rule right to left
  (`join_usable`). Joins are memoized per pair in `RewriteMemo.joins`, invalidated like other entries.
- **Exact miner first** (every failed or met join traces all it examined; run `2026-10-17-join-memo`, salts 1-10 against
  8d5b29d, CPU 14% at launch, RTP off): M mines 2 to 0, own 13 to 26, cold 1568 to 1563, pooled 33 to 36; summed mine
  time 33 to 51 s. Almost every candidate touches the many terms a met join examined, so its memo entry was rerun.
- **Option 1, built:** a met join traces only the terms on its path and their subterms. Its entry is dropped when a
  rule added or removed matches one of them, and kept when the rules added act only elsewhere in what the search
  examined. Inexact: those added rules widen the search's frontiers, so a pair that met can reach `JOIN_VISIT` before
  meeting, and serving then fails where the miner counted it joined. Tests: `failed_join_traces_every_term_it_examines`,
  `met_join_traces_its_path_only`.
- **Results** (run `2026-10-17-join-sticky`, salts 1-10, against 8d5b29d, CPU 17% at launch, RTP off): every salt's M
  and every stage's rule count are those of the exact miner (mines 0, own 26, cold 1563, pooled 36; rules 383, 1165,
  640, 3259); summed mine time 46 s (exact 51, blind 33). `ABLATE=join` on both builds gives identical rows
  (`2026-10-17-join-sticky-ablate`). With `JOIN_CHECK` (`docs/runs/2026-10-17/patches/join_check.patch`: on every memo
  hit of a met plan, search again under the current rules; run `2026-10-17-join-sticky-flips`), no kept plan failed in
  at least 230000 hits over the 10 salts.
- **The mine's time is the join's searches; the gain bound saves none of it** (run `2026-10-17-join-time`, salt 6's
  cmp3d mine alone, build `bv_jtime.exe` with `patches/no_bound.patch`, CPU 24% at launch, RTP off). Measured in a job
  object (`tools/runs`, `runs run`, two runs in the run's `job.txt`), the stage (the mine and serving its batches)
  took 25.3 and 29.9 CPU s in 6.9 and 8.2 s of wall, of which the mine's join searches 21.2 and 25.0 s (84%), failed
  ones 6.6 and 7.9 s (26%); rule-set evaluations and bounding took 0.4 s each. Scoring every candidate (`RULEMINER_NO_BOUND`, 4 runs each way, alternated)
  mines the same rules: 15158 scorings against 11357, 76800 searches against 74760, join time 22.6-26.9 s against
  23.1-35.1 s, wall 7-10 s either way. The candidates the bound skips touch few laws, so they cost few searches. The
  searches: 74760 reaching 10.1M terms, 94.5% met, 35783 memo hits. Each scoring worker starts each pick with a fresh
  memo (expressions are interned per thread), so the same pair is searched again in each pick.
- **Carrying the workers' memo across rounds saves little; reusing serving's joins saves nothing** (run
  `2026-10-17-join-pool`, `join_ab.sh` with c87573b's build `bv_jtime.exe` against the `score-pool` spike ported onto it,
  `patches/score_pool_join.patch`, salts 1-10, CPU 14% at launch, RTP off). Workers alive for the whole search, each
  dropping at a new round only the entries a rule in or out touches: every stage's M and every rules file equal; mine
  join searches 588769 to 568676 (-3.4%), salt 6's cmp3d mine 74757 to 70879 with 39.1 against 37.7 s searching; mine
  time 52 s both, sweep wall within 1 s per salt. A chosen rule touches most join traces, so few entries outlive a round.
  Reverted. Serving: served batches are disjoint stream slices, so no pair repeats across them, and serving's joins over
  the 1090 batches of `2026-10-17-join-sticky` (arm b) reached 1.36M terms, about 4 s in all. Both are `decided against`
  in `PARKED.md`.
- **The interner's per-thread cache: the join's time was building terms, and a cache in front of the shared table cuts
  the mine's CPU by a third.** A samply profile of salt 6's cmp3d mine (run `2026-10-17-join-prof2`,
  `scripts/join_prof.sh`, the throwaway test in `patches/join_prof.patch`; `join-prof`, the run before it, passed its
  test name wrongly and profiled nothing) put 58% of the busy samples under `Term::op` (43% in its own frame, 11% in
  the shard mutexes' contention), 37% of them through `join_steps` rebuilding a neighbour's spine and 21% through
  `subst_pat`; `match_pat`'s own frame was 8%. A count (`patches/op_cache.patch`, its `OPPROBE` line) found 167M
  `Term::op` calls in that mine, 97% from the join and 99% finding an existing node: about 16 per term the join reached
  (10.1M). `Term::op` now first tries a per-thread slot array (`OP_CACHE`, 2^16 slots by bits 44..60 of the hash, a hit
  when the slot's node is the one asked for), then the shared table, and keeps the result in the slot. Nodes are never freed, so a cached node is the term's one node and
  outputs cannot change. Timed by `scripts/op_cache.sh` (run `2026-10-17-op-cache`, `runs time`, 5 arms alternated, 3
  clean rounds, CPU 9%, RTP off), job CPU median of salt 6's cmp3d stage:

  | slots | job CPU s | wall s | join searching s |
  |---|---|---|---|
  | off | 25.8 | 7.0 | 21.4-23.0 |
  | 2^12 | 18.2 | 5.5 | 14.0-18.9 |
  | 2^14 | 17.4 | 5.5 | 13.0-16.1 |
  | 2^16 | 16.9 | 5.3 | 12.6-14.5 |
  | 2^18 | 17.4 | 5.4 | 12.6-14.7 |

  Rules equal in all 25 runs; peak job memory about +20 MB. Over salts 1-10 (run `2026-10-17-op-cache-ab`, `join_ab.sh`,
  c87573b's build against it) all 2430 stage, rules and law files are equal but for their time columns, and the arms'
  times (run side by side, so only rough) sum to 77 s against 86 of wall, mines 30 s against 35. Early cuts of failed
  searches are still open, now on about 60% of the old search time.
- **Kernel cost of a joined proof against the machine proof it replaces** (run `2026-10-17-join-proof-cost`,
  `scripts/join_cost.sh`: `proof_cost_split` on every served cmp3d batch of `2026-10-17-join-sticky`'s loops, salts
  1-5, 135 batches, under each loop's final rules, with the join on and with `ABLATE=join`, the faster of 2 alternated
  runs per batch; CPU 10% at launch, RTP off). With the join on, 3375 laws are joined and 13 need a machine proof;
  with it off, 3388 need one. Per joined law: build 7.7 ms against 21.5 ms for the machine proof, check 0.49 against
  0.47 ms, 965 against 889 unique nodes. The rules-only laws (10112, the same in both arms) differ by 10% in build time
  between the arms, so the check times are equal within noise; building is 2.8 times cheaper.
- **Cost reporting.** The mine log has `RULEMINER join: <searches> searches reaching <terms> terms, <met> met, <hits>
  memo hits, <s>s searching (<s>s in failed searches)` (workers' counts summed, `JoinCost`) and the time spent bounding
  candidates' gains. The sweep's stage files gain columns for the laws joined and the terms the joins reached.
  `proof_cost_split` has a joined row.

### The law generator and its filter (2026-10-17 to 10-22)

*A law generator: stream-blind laws one grown leaf from the pool match the stream's own unseen laws (2026-10-17).* The
extras that cut M in "What kind of new law pays most" came from the stream itself (phases no loop serves). A generator
must not read the stream. `search::grammar_laws` is the first stream-blind source: it takes the family's pool, grows one
leaf of a pool term into a depth-1 term over the operators the pool uses (`lt` excluded: its result is one bit wide),
samples about `GEN_TERMS` such terms (default 20000) by a hash of the salt, groups them with the pool by width-4 values
(`pool_conjectures`), and keeps the pairs that have a grown side and use all three variables between their two sides,
shuffled by the salt. Every pool is closed under renaming variables (each leaf slot ranges over x, y and z), so no such
law is a stream law or shares a stream law's skeleton (argued from the construction; no test checks the skeletons). By
the bucket probe's skeletons they are all `novel`, which paid little there (M 951, past 966, unseen 581). A law is
*padding* when a grown side's leaf grew into a term equal to a leaf (`sub(y, y)`, `and(0, -1)`, `or(-1, z)`), e.g.
`or(x, z) = add(or(z, x), sub(sub(y, y), 0))`; `GEN_PAD=pad|nopad` keeps only those laws or only the rest
(`grammar_pad_splits_the_laws`: at 3000 terms, 240 of add3's 438 laws and 378 of cmp3d's 876 are padding).

`driver::extra_laws` is one extras pipeline with two sources: `MINE_EXTRA=<family>:<n>,...` adds n laws to each cold loop's
mine from `MINE_SOURCE=stream` (the bucket probe's `unseen` arm, rebuilt on the current code) or `grammar` (the loop's slice
of `grammar_laws` at its phase), and keeps a law only if it is twin-free against the served phases 1-3 and its skeleton is
not among the mine's own laws (filters the grammar source passes by construction). Full counts as before: add3 60, sbo3
180, cmp3d 350 per mine; every source filled them. Cold sweeps, sequential (runs `2026-10-17-gen-src`, salts 1-10, CPU
29% at start; `-gen-cost`, salts 1-10, 34%; `-gen-salts`, salts 11-20, 67%; RTP off in all; M is deterministic, the
times are not, and compare only within a run):

| arm | salts | mined-batch M | cmp3d | add3 | sbo3 | per salt | rules | loop seconds |
|---|---|---|---|---|---|---|---|---|
| plain | 1-20 | 221 | 167 | 14 | 40 | 3-24 | 1242 | 5 |
| stream (`unseen`) | 1-20 | 44 | 35 | 3 | 6 | 0-9 | 2319 | 98 + 110 |
| grammar | 1-20 | 28 | 19 | 9 | 0 | 0-5 | 3776 | 506 + 673 |
| grammar, padding only | 1-20 | 27 | 23 | 4 | 0 | 0-7 | 2486 | 166 + 204 |
| grammar, no padding | 1-10 | 9 | 8 | 0 | 1 | 0-3 | 2483 | 1373 |
| grammar, half counts | 1-10 | 33 | 25 | 4 | 4 | 0-8 | 1352 | 229 |
| grammar, quarter counts | 1-10 | 64 | 53 | 6 | 5 | 0-17 | 1012 | 67 |

Loop seconds split by run (salts 1-10 + 11-20); the salts 1-10 of the padding-only, no-padding, half and quarter arms ran in
`-gen-cost`, the rest in `-gen-src`. On salts 1-10 stream had 29, grammar 12; on salts 11-20, 15 against 16.

- **The stream-blind source ties with the stream's unseen laws; it does not beat them.** Over 20 salts grammar is better
  on 9, equal on 5 and worse on 6; the first ten salts' 12 against 29 came mostly from salts 7 and 9 (stream 9 and 5,
  grammar 0 and 0). Without those two salts: stream 30, grammar 28, padding only 27. The skeleton reading's prediction
  (novel shapes pay little) still fails: laws one grown leaf from the pool pay as well as the stream's own unseen shapes.
- **Padding only is the cheap slice, not the best one:** M 27 against stream's 44 (better on 10 salts, equal on 5,
  worse on 5) at 7% more rules and 1.7-1.9 times the loop time (166 against 98 s on salts 1-10, from two runs and two
  builds, the grammar arms' with `GEN_PAD` added; 204 against 110 s on salts 11-20, one run at 67% CPU). The full grammar
  costs 63% more rules and 5-6 times the time for about the same M; padding against the full grammar (16 against 12 on
  salts 1-10, 11 against 16 on 11-20) is within the noise.
- **No padding gives the lowest M (9 on salts 1-10, not run on 11-20) at 14 times the stream's time,** with the miner
  keeping 2483 rules (why so many was not traced). So per law the non-padding laws pay at least as much; padding is
  chosen for cost. Why padding laws pay: see the next note (much of it is twins of served laws in disguise); filtered alike, they lose
  to the stream and the mixed grammar wins (the note after it).
- **Fewer laws lose part of the gain:** half counts still cut plain's 120 to 33 (at 2.3 times stream's time) but do no
  better than stream; a quarter gives 64.
- Generating costs 0.1-0.6 s per family (`GEN_LAWS` lines), against loop seconds in the hundreds, so nearly all the extra
  time is mining (not measured apart). Batch 0's M is the same in every arm
  of a run (1443 on salts 1-10, 1408 on 11-20), so the extras act only through mining. The headroom is about a tenth of
  what it was (plain 120 on salts 1-10 against 1169 at 9c601c3; the join and the other changes since were not
  separated), so the counts are small: a tie is the reading, not a ranking among the grammar arms.

*Why padding laws pay: about a quarter are served laws in disguise (2026-10-17).* A padding law is a pool term set equal
to another pool term with one leaf written as a term of equal value, so stripping the padding (each node over two
leaves whose width-4 value equals a leaf becomes that leaf) gives a law between two pool terms. The twin-free filter
compares text up to renaming, so it cannot see through the padding. Stripped and keyed as the filter keys laws
(`scripts/pad_strip.py`, over the padding arms' extras), per 10 salts:

| family | extras | twin of a served law | of which the loop's own later batches | strips to `a = a` | other |
|---|---|---|---|---|---|
| cmp3d | 10500 | 2576 (25%) | 576 | 1678 | 6246 |
| add3 | 1800 | 656 (36%) | 98 | 292 | 852 |
| sbo3 | 5400 | 1530 (28%) | 302 | 1272 | 2598 |

(Salts 1-10 from `-gen-cost`; salts 11-20 from `-gen-salts` give the same shares within 1-2 points.) "Served" is any
batch of a phase 1-3 loop of the family, the set the filter guards; the rest of the twins are the loop's own mined batch 0
and other loops' batches. The mined rules carry no padding: no rule of the padding, plain or stream arms has a same-leaf
(`sub(x, x)`) or identity (`add(x, 0)`, `and(x, -1)`) subterm.

The causal test (run `2026-10-17-gen-twin`, `scripts/gen_twin.sh` with the throwaway `patches/extra_file.patch`,
`MINE_SOURCE=file` reading extras from files written by `scripts/pad_files.py`; salts 1-10, sequential, CPU 26% at start,
RTP off):

| arm | mined-batch M | cmp3d | add3 | sbo3 | per salt | rules | loop seconds |
|---|---|---|---|---|---|---|---|
| padding laws, replayed from the files | 16 | 16 | 0 | 0 | 0-5 | 1220 | 142 |
| the stripped twins dropped | 30 | 23 | 0 | 7 | 0-9 | 1028 | 85 |
| as many other laws dropped (fixed hash) | 14 | 10 | 3 | 1 | 0-4 | 1052 | 73 |
| stream (`unseen`, `-gen-src`) | 29 | 20 | 3 | 6 | 0-9 | 1163 | 98 |

- **The replay is exact:** all 90 rule files equal the `-gen-cost` padding arm's, so the file source changes nothing.
- **The twins carry the padding arm's edge over the stream.** Dropping them takes M 16 to 30; dropping as many
  other laws leaves 14 (twins dropped is worse on 4 salts, better on 1, equal on 5 against that control). Untwinned, the
  padding laws seemed to match the stream's unseen laws (30 against 29) with 12% fewer rules, but the stream arm was not
  filtered the same way, and the strip missed twins: see the next note, where the fair comparison has the padding laws
  losing.
- A generator proposes laws from the family's own pool, which is the stream's universe, so it will propose served
  laws; a fair measurement must filter them up to equal-valued subterms, not up to text, and filter every arm alike.

*One filter for every source: with twins removed alike, the padding laws lose to the stream and the wider grammar
wins (2026-10-17).* The strip above has two gaps: it normalizes the extras but not the served laws (which hold padding
nodes too: 5164 lines of the padding arms' served files have a same-leaf or identity node), and it only maps nodes equal
to a leaf. `scripts/twin_wide.py` normalizes every node over two leaves (`lt` aside) to its width-4 value class's
representative (a leaf if one is in the class, else the shortest, then least, two-leaf term), on both sides, and keys
the result as the filter does. Twins of a phase 1-3 served law, per 10 salts (cmp3d, add3, sbo3 summed: 17700 extras per
arm):

| source | twins: extras stripped (above) | both stripped | value classes, both sides | trivial after normalizing |
|---|---|---|---|---|
| padding laws (`-gen-cost` pad) | 4762 | 7870 | 7423 (42%) | 5413 |
| mixed grammar (`-gen-src` grammar) | 1867 | 3109 | 2933 (17%) | 2322 |
| non-padding laws (`-gen-cost` nopad) | 5 | 11 | 22 (0.1%) | 269 |
| stream's unseen laws (`-gen-src` stream) | 2091 | 6259 | 8467 (48%) | 3912 |

So the stream's own unseen laws, filtered twin-free as text, are half served laws behind equal-valued two-leaf nodes,
more than any generator's. The causal test replays each source with its class twins dropped (run
`2026-10-17-gen-wide`, `gen_twin.sh` with `ARMS` over the files of `scripts/wide_files.py`, build `bv_padfile.exe` as in
the note above; salts 1-10, sequential, CPU 13% at start, RTP off):

| arm | mined-batch M | cmp3d | add3 | sbo3 | rules | loop seconds |
|---|---|---|---|---|---|---|
| stream, replayed | 31 | 22 | 3 | 6 | 1155 | 86 |
| stream, class twins dropped | 29 | 14 | 9 | 6 | 895 | 40 |
| padding laws, class twins dropped | 40 | 22 | 9 | 9 | 957 | 51 |
| the same, trivial laws dropped too | 42 | 24 | 9 | 9 | 933 | 49 |
| the same, as many other laws dropped instead | 83 | 47 | 9 | 27 | 709 | 5 |
| mixed grammar, replayed | 12 | 8 | 4 | 0 | 1889 | 413 |
| mixed grammar, class twins dropped | 21 | 16 | 4 | 1 | 1859 | 359 |
| non-padding laws (`-gen-cost`, another build) | 9 | 8 | 0 | 1 | 2483 | 1373 |
| non-padding laws, class twins dropped (22; `-gen-nopad`) | 10 | 9 | 0 | 1 | 2478 | 1043 |

- **The replays are exact within a build, not across builds.** A second run of the stream replay's salt 1 gave the same
  rule files; against `-gen-src` (da775e7 plus the probe), 6 of the stream replay's 90 rule files and 2 of the
  grammar's differ, and M moves by 1 on salts 1 and 4. Each comparison below is within this run's one build.
- **Twins pay only behind padding.** Dropping the stream's twins costs nothing (31 to 29, half the loop time);
  dropping the padding laws' costs 16 to 40 (with the strip's twins alone, 30). The mixed grammar loses 12 to 21.
- **Fairly filtered, the padding laws lose to the stream:** 40 against 29, worse on 6 salts, better on 3, equal on 1.
  The mixed grammar beats the stream (21 against 29: better on 6, worse on 2, equal on 2), at 9 times its loop time. The
  non-padding laws, which hide almost no twins, have the lowest M: replayed with their 22 twins dropped (run
  `2026-10-17-gen-nopad`, same build and script, salts 1-10, CPU 14% at start, RTP off), 10 against the stream's 29
  (better on 6 salts, equal on 4, never worse), with 2478 rules against 895, at 26 times the filtered stream's loop
  time (1043 against 40 s).
- **Trivial laws barely pay:** a law whose sides normalize to the same term (24-42% of the padding laws per family)
  is an identity of two-leaf nodes in context. Dropping them costs 40 to 42 and saves little time. The control (dropping
  as many of the other laws) is matched on cmp3d only: add3 and sbo3 have fewer other laws than trivial ones, so it
  drops all their other laws.
- Not covered: a grown node equal in value to a deeper subterm of a pool term (only two-leaf nodes are normalized).

*Where an extras mine's time goes (2026-10-17, from the runs above, no new run).* Every mine's time is still the join's
searches (`RULEMINER join` lines, the first mine of salt 6's cmp3d phase 1 loop unless noted), 1.5-3 µs per reached term
(summed over the scoring workers); extras multiply the searches and their reach:

| mine's laws | searches | terms reached | per search | search CPU s | in failed searches |
|---|---|---|---|---|---|
| plain (100) | 4208 | 0.47M | 111 | 0.7 | 29% |
| stream (+350) | 26903 | 3.89M | 145 | 8.3 | 40% |
| padding (+350) | 28442 | 3.60M | 126 | 10.5 | 23% |
| mixed grammar (+350) | 69541 | 16.4M | 236 | 31.2 | 48% |
| non-padding (+350) | 117210 | 30.9M | 264 | 91.9 | 31% |
| non-padding, sbo3 (+180) | 70884 | 18.7M | 264 | 56.2 | 37% |

Law evaluations are 94% reused (non-padding cmp3d: 2241297 of 2394280), the gain bound and rule-set evaluation take
about 2 s of the 92, so the levers are the searches themselves (how busy the 6 scoring threads stay was not measured):
fewer terms built per visited term (99% of `Term::op` calls find an existing node, "The interner's per-thread cache"),
early cuts of failed searches (`PARKED.md`, now on 23-48% of search time), or an order that meets sooner (inexact:
it changes which pairs meet within the cap).

*Profile of an extras mine (2026-10-18, run `2026-10-17-gen-prof`).* samply over salt 6's cold cmp3d loop with the
non-padding extras, class twins dropped (`gen_twin.sh`'s nopad_class files; `patches/gen_prof.patch` on
`extra_file.patch`, a5ade34's code, debug info; CPU 12% at start, RTP off). Its first mine is the table's non-padding
row (117220 searches, 30.9M terms). Of 204253 busy samples over the loop's three phases (frames in
`docs/runs/2026-10-17/rows/2026-10-17-gen-prof.txt`):
- the join is 89.5% inclusive (`join_eq`; `join_steps` 85.5%); the rest of the miner, the kernel checks and the
  rewriting add up to under 10%;
- `Term::op` is 43.8% self (48.8% inclusive), called from `join_steps` (29.8% of all samples) and `subst_pat` (13.7%);
  `match_pat` 13.8% self; the interner's lock waits are 2.2% (11% in the ref mine's profile before the op cache).

So an extras mine has the ref mine's shape, only more of it: the levers above stand, with term building (`Term::op`
from the join's rewrite steps) first.

*The law generator as a stage (2026-10-18, plan `docs/superpowers/plans/2026-10-17-law-generator.md`).* Every mine with
rule rounds now also mines a slice of the generator's non-padding laws (`driver::scope_extras`), filtered against the laws
its scope serves by value-class twin key (`ClassReps`) and by skeleton. Cold sweeps, mined-batch M (scripts in
`docs/runs/2026-10-17/`, rows in its README):
- **Checks** (run `2026-10-18-gen-check`): with the stage off (`ABLATE=gen`) every rule file equals the build before it
  (`-gen-check-plain`) on 10 of 10 salts; with the probe's counts (`GEN_COUNTS=legacy`, since deleted) it equals
  `-gen-cost`'s nopad arm on 9 of 10, salt 4's one differing rule file being build drift since 4346cda (`-gen-check-s4-*`).
- **Probe** (salt 1, CPU 88% from other sessions): wall seconds off 12, f04 78, f08 90, s08 98, s16 285. The stream
  control could not run at the generator's n: the filter leaves the unserved stream phases 292 / 42 / 166 laws (cmp3d /
  add3 / sbo3) against 6n = 1134 / 450 / 444 at f 0.04. So the control is a matched pair: `GEN_N=matched` caps n at what
  the filtered stream fits, for both sources (m08 and stream_m08).
- **Round A** (salts 1-10, run `2026-10-18-gen-round-a`; f = share of the filtered list, fresh slices per mine or shared
  per loop):

| arm | M (cmp3d add3 sbo3) | rules | loop s | vs s16: better / equal / worse |
|---|---|---|---|---|
| s16 (shared, 0.16) | 5 (5 0 0) | 4141 | 4029 | |
| legacy (probe counts) | 9 (8 0 1) | 2468 | 929 | 1 / 4 / 5 |
| f08 (fresh, 0.08) | 17 (17 0 0) | 3270 | 1048 | 0 / 6 / 4 |
| s08 (shared, 0.08) | 23 (22 0 1) | 2804 | 1082 | 0 / 4 / 6 |
| f04 (fresh, 0.04) | 35 (32 0 3) | 2213 | 297 | 0 / 2 / 8 |
| m08 (f08, matched n) | 88 (65 10 13) | 1071 | 20 | 0 / 0 / 10 |
| stream_m08 | 92 (56 9 27) | 689 | 2 | 0 / 0 / 10 |
| off | 120 (84 9 27) | 640 | 9 | 0 / 0 / 10 |

- **Round B** (salts 11-20, run `2026-10-18-gen-round-b`), over salts 1-20: s16 11 (rules 8490, loop s 7786), m08 155,
  stream_m08 183, off 221; s16 beats each on all 20 salts. Round B's off equals `-gen-salts`' plain (101).
- **Default: s16**, the only arm with no more salts worse than better against the best. The share, not fresh slices,
  carries the gain: at f 0.08 fresh beats shared (17 against 23), but shared at 0.16 beats both.
- **Acceptance** (the spec: the generator beats the stream at the same n): m08 against stream_m08 over salts 1-20, better
  on 13, equal on 2, worse on 5. The stage stays on by default. This checks the source at the stream's small n (fresh
  slices, salt 1: n 48 / 7 / 27 for cmp3d / add3 / sbo3, against s16's hundreds), not the chosen arm, and 13 against 5
  is a weak sign (two-sided sign test p ≈ 0.1); the stage's worth rests on s16 against off (20 salts of 20).
- **Cost**: s16's loops take 7786 s over 20 salts against off's 9 (the probe's sweep wall time 285 s against 12), all in
  the join's searches ("Where an extras mine's time goes"). Numbers from here on are with the stage on unless they say
  `ABLATE=gen`. Ref mines and warm loops take extras too but are unmeasured (the spec's step 4, `PARKED.md`): until
  then, sweeps with a `mines` stage or warm loops run with `ABLATE=gen` or after a 1-salt probe. (Measured since: the
  next section.)

*The law generator on ref mines and warm loops (2026-10-22, plan `docs/superpowers/plans/2026-10-22-generator-warm-ref.md`,
runs `2026-10-22-gen-warm-probe` (salt 1) and `2026-10-22-gen-warm` (salts 2-10), script
`docs/runs/2026-10-22/scripts/gen_warm.sh`, table `gen_warm_table.sh`; build 7beda97's tree, CPU 23% for the probe and
100% from other sessions for the rest, Defender real-time off).* The stage pays in all three regimes, so it stays on
everywhere. Per salt, the ref mines ran with the generator on (`mon`) and off (`moff`), and the loops (`own cross pooled
mixed`, plus `cold` in two arms) read those libraries through `LIB=` with their own extras on or off: a 2×2, arms
`<library>_<loop extras>`. On add3 the split sweeps reproduce one combined sweep (library and loop rules equal). Loop M
summed over salts 1-10 (total; mined-batch M, batches 1-2 counted from 0, in brackets):

| stage | on_on (default) | off_on | on_off | off_off (`ABLATE=gen`) |
|---|---|---|---|---|
| own | 4 (4) | 17 (7) | 5 (5) | 26 (16) |
| cross | 685 (19) | 797 (15) | 849 (183) | 977 (195) |
| pooled | 21 (9) | 35 (26) | 15 (3) | 36 (27) |
| mixed | 25 (4) | 25 (10) | 42 (21) | 28 (13) |
| cold | 1451 (8) | | | 1563 (120) |

- **Ref mines, judged by the loops they seed** (on_on against off_on, salts better / equal / worse): own 5/4/1, cross
  10/0/0, pooled 7/0/3, mixed 5/2/3. Their own M is 0 in both arms but for u3 (8 against 1 over 10 salts). With the
  loops' extras off, the generator's libraries lose in mixed (on_off 42 against off_off 28, 2/5/3), mostly at salt 2 (19
  against 2). A guess, not tested: the generator's share of a ref mine is smaller (n about 240-800 extras per ref mine
  against its b × k = 200-400 laws, where loop mines' 290-793, varying by salt, face a batch of 100), and u3, whose ref M
  is 5 against 0 at salt 2, is where that shows. Ref mines also mine more rules (summed: add3 265 against 29, mix3 290
  against 0).
- **Warm loops' own extras** (on_on against on_off): own 2/7/1, cross 10/0/0, pooled 1/5/4, mixed 5/5/0; over the four
  stages M 735 against 911, of which cross carries 164 (685 against 849); own ties (4 against 5). Pooled is the one stage that loses (21 against 15, mined 9 against 3); a guess at why: its library
  already holds three families' rules, and the extras add mined rules that conflict with them. Weak (4 worse, 1 better; two-sided sign
  test p ≈ 0.4) and below the regime: turning extras off for one stage would be a per-stage case, so it is parked
  (`PARKED.md`, "Extras on a warm stage that loses"; decided against when the warm stage went with the families, entry deleted 2026-10-27).
- **Both** (on_on against off_off): own 7/3/0, cross 10/0/0, pooled 5/1/4, mixed 4/3/3, cold 10/0/0.
- **Cost** (wall over 10 salts, CPU saturated by other sessions, so an upper bound): ref mines 349 s against 29, loops
  1225 s against 26 (cold included in both), job CPU 1635 + 8721 s against 65 + 71. mix3's generator list (never built
  before) is 1669 laws in 0.2 s, L 1644; u3's 1877 in 0.3 s; peak job memory 2.1 GB.
- So the default stays: every mine with rule rounds takes extras. Hidden twins (the spec's step 5) are next.

*Hidden twins beyond two-leaf nodes (2026-10-22; spec step 5; run `2026-10-22-gen-warm-fix` at 199135b, script
`gen_warm.sh` with `ARMS="on_on off_off"`, salts 1-10, 17 min wall, CPU 26% at launch, Defender real-time off).* The
twin filter normalized only nodes over two leaves. `ClassReps` now normalizes every node below a law's root: to the least
term of its width-4 class among the leaves, the two-leaf terms and the family pool's subterms, or else to a child of equal
value (`add(t, 0)` to `t`); the root and an `lt` stay. The filter drops an extra whose key is a served law's (a twin) and
an extra whose sides are equal once normalized (trivial).
- **Count** (`hidden_twins_in_a_run`, over the extras step 4's on_on and mon arms drew, salts 1-10): 11.0% of the loops'
  extras twin a served law (add3 11.5%, sbo3 17.0%, cmp3d 8.5%) and 8.6% of the ref mines' (6.9% cmp3d to 12.2% mix3),
  in every family, such as `sub(add(x, y), add(x, z))` for `sub(y, z)` in a served cmp3d law. A further 30% of the loops'
  extras are trivial (cmp3d 40%). Over the new run's extras the count is 0 twins and 0 trivial, as it should be. Of the
  served laws 27-69% are trivial (cmp3d's most), so they block no twins.
- **L halves** (salt 1, loops: cmp3d 4737 to 2359, add3 1885 to 1422, sbo3 1862 to 1151; ref mines: u3 1872 to 975, mix3
  1644 to 996), so n = ⌊0.16 L⌋ halves too: the loops mine on half as many extras, not only on different ones.
- **Effect** (salts 1-10, the generator on everywhere, against step 4's on_on, better / equal / worse): warm M 735 to 754
  (4/1/5), cold 1451 to 1475 (1/5/4); mined-batch M rises in each (warm 36 to 69, cold 8 to 32). Per stage: own 4 to 3,
  cross 685 to 707, pooled 21 to 8 (6/4/0), mixed 25 to 36 (3/3/4). Twins removed and n halved are
  separated below ("The generator's n after the wider filter"): the rise is mostly the halved n.
- **The generator still pays** (on_on against off_off, both on this build): warm 754 against 1067, better on 10 salts of
  10 (own 6/4/0, cross 10/0/0, pooled 8/1/1); cold 1475 against 1563, 9/0/1. Mixed is the one stage that loses, 36
  against 28 (0/7/3, sign test p ≈ 0.25). Ref mines' own M is 0 in both arms but for u3 (1 against 1).
- **Cost** (wall over 10 salts): ref mines 217 s against 27, loops 617 s against 28, job CPU 4769 s against 62; loop
  seconds warm 404 against 0, cold 546 against 14. Step 4 took 1225 s for its on_on loops, at 100% CPU from other
  sessions, so the halving is not timed.
- **A miner hang, found on the way** (run `2026-10-22-hidden-twins-2`, cc2cab5, killed): on_on salt 10's
  `mixed_cmp3d` mine 1 re-chose `add(0, x) -> x`, a rule it already had, 8631 times at +0 fixed. A memo hit on a failed
  join returned the failure without asking the join store, which grows as searches feed it; `state`'s seeded memo kept
  such failures while the scoring workers, reading the round's store, met the pairs. Claimed gains then exceeded
  realized ones (2065 against 1065 in that mine's round 3), and a chosen rule, which changes nothing, won every round.
  Fixed in `join_eq` (60d8116: a cached failure yields to a stored path; the mine then ends in 2 s with an unseeded
  state's choices, every claimed gain realized), and a round no longer offers a chosen rule (199135b, `by_bound`), nor a
  chosen rival (c59107a, `best_rival`: under exact scoring a chosen rule gains 0, so neither guard moves M). The fix
  changes no M elsewhere: off_off equals step 4's on every salt and stage, on_on equals that run's on salts 1-9.
- **What was wrong before** (b5e03cd, run `2026-10-22-hidden-twins`): its key normalized the root too, so a pool law's
  two sides fell in one class and most served laws became trivial; trivial laws were kept and blocked nothing, so the
  filter barely filtered (cmp3d 8.6% dropped, add3, sbo3 and mix3 none). Its numbers (cold 1474, warm 788) and its
  "none of add3's, sbo3's or mix3's" are void; cc2cab5 keeps the root and drops trivial laws.
- The probe fixture's count (`normalize_finds_the_probes_twins`) is 443 twins and 409 trivial laws against
  `twin_wide.py`'s two-leaf 502 and 260.
- So the wider filter stays, and v0.2 is answered: the law generator pays on cold loops, warm loops and ref mines,
  measured with no served law in disguise among its extras; mixed loops are the open exception.

*The generator's n after the wider filter (2026-10-22; run `2026-10-22-gen-f32` at 708cd43, `gen_warm.sh` with
`ARMS=on_on GEN_F=0.32`, salts 1-10, 49 min wall, CPU 60% at launch, Defender real-time off).* The wider filter halved
L and so n; this arm doubles f (the variable `GEN_F`, 488307b) to separate the two. Against the two-leaf filter's n
(salt 1) the new n is 1.0x on cmp3d (754 against 757), 1.24x on sbo3 and 1.51x on add3: at or above the old n.
- **Against f = 0.16** (run `2026-10-22-gen-warm-fix`, better / equal / worse): warm M 754 to 729 (7/1/2), cold 1475
  to 1460 (6/2/2); mined-batch M 69 to 54 and 32 to 17. Own 3 to 4, cross 707 to 692, pooled 8 to 7, mixed 36 to 26.
  Neither count is strong alone (sign test p ≈ 0.18 and 0.29), but every stage but own moves the same way.
- **Against step 4** (two-leaf filter at its own n): warm 735 to 729 (7/0/3), cold 1451 to 1460 (2/2/6). At about the
  old n, removing the twins is near neutral; step 5's rise in M was mostly the halved n. Mined-batch M stays above
  step 4's (warm 54 against 36, cold 17 against 8).
- **Against the generator off** (off_off of `gen-warm-fix`): warm 729 against 1067 and cold 1460 against 1563, both
  better on 10 salts of 10; mixed 26 against 28 (3/5/2), so mixed no longer loses at this n. Ref mines' own M is 0 in
  every family.
- **Cost** (loops, 10 salts): wall 2296 s against 617, job CPU 15547 s against 4769, loop seconds warm 1844 against 404
  and cold 2200 against 546; ref mines' wall 546 s against 216. The load was 60% against 26%, so job CPU (3.3x) is the
  fairer ratio.
- So removing the twins is near neutral, and the halved n cost 1-3% of M (warm 3.3%, cold 1.0%) at a third of the CPU.
  `GEN_F`'s default stays 0.16 for now (`PARKED.md`, "The generator's n after the wider filter").

*How much choosing the extras can gain: redrawn generator lists (2026-10-22; runs `2026-10-22-gen-draw1` to `3`,
`gen_warm.sh` with `ARMS=on_on GEN_DRAW=1..3`, exe at 6d9e004, salts 1-10; draw 0 is `gen-warm-fix`'s on_on).*
`GEN_DRAW=d` hashes the generator with salt + 1000·d, so the sample and its order are redrawn (L moves a few percent;
salt 1 cmp3d 2346 to 2485) while the stream, the miner and the loops keep salt s; the ref mines (`mon`) take the draw's
extras too. n stays at f = 0.16. The spread across draws bounds what a ranker over the generator's laws could gain at
this n (ROADMAP v0.3's gate).
- **Totals** (warm M with mined-batch M in brackets; cold the same): draw 0 754 (69) and 1475 (32); draw 1 749 (69) and
  1467 (24); draw 2 766 (80) and 1473 (30); draw 3 739 (58) and 1462 (19).
- **Batch 0 does not move.** Cold batch 0 is 1443 in every draw (no rules, as it must be); warm batch 0 is 680-686
  although the ref libraries were mined on each draw's extras. A choice of laws barely changes what a ref library is
  worth on the next family's first batch.
- **The spread is all in the mined batches.** The best draw per salt, chosen by its own test batches (an oracle over
  four draws), gives mined-batch M 38 against 69 (warm) and 12 against 32 (cold): about half of mined-batch M, 51
  laws of about 2230 in total M. Summed per-salt spread (worst minus best) is 89 warm and 35 cold. Not a strict bound:
  a ranker could compose a set better than any of the four draws.
- **Cost does not move.** Job CPU of draws 1-3 is 6285-6582 s (within 2.5%). Loop seconds spread 1.7x (warm 404-676,
  cold 546-986), but they follow the load at launch (26% for draw 0 against 35-63%), not the draw.
- So at this n a ranker over which generated laws to mine on can gain at most a few percent of M and no cost; the
  levers left are a smaller n at equal M (not tested here) and new vocabulary (goal 2, `ROADMAP.md`; its enumerator form was decided against in v0.4, "They do not transfer").

### The frontier by law size, and the join's budget (2026-10-22)

*Free proofs by law size: a gradient for the frontier (2026-10-22; run `2026-10-22-size-band`, 49 s, CPU 51% at
launch; probe `docs/runs/2026-10-22/patches/size_band_probe.patch`, reverted).* Serving never fails to prove a law:
the whole-term machine proof closes whatever rewriting and the join leave, and all 194 serves of `gen-warm-fix`'s salt-1
loops and ref mine report 0 not proved. So a frontier ("the hardest law provable within a budget", the v0.5.0 tag) has to count proofs with no
machine proof. The probe (`search::size_band_laws`) grows each family's pool twice, one leaf at a time into an
operator over two leaves (padding growths dropped, about 20000 terms per level, salt 11), pairs terms by width-4
values as `grammar_laws` does, and keeps up to 200 laws per size (the larger side's nodes; odd, since every operator
is binary). Laws the salt-1 ref mine had mined on are dropped. `size_band.sh` serves each size with no mined rules and
with the family's salt-1 ref library (`gen-warm-fix`, `mon_1`). Free share (free / proved), none and ref:

| family | size 7 | size 9 | size 11 | size 13 |
|---|---|---|---|---|
| add3 | .77 / .91 (57 laws) | .76 / .95 | .56 / .80 | |
| sbo3 | .83 / .96 (126) | .70 / .88 | .64 / .82 | |
| mix3 | .90 / .92 (184) | .73 / .84 | .71 / .78 | |
| cmp3d | .82 / .86 (22) | .79 / .99 | .67 / .98 | .56 / .93 |

- **Not falsified: there is a gradient.** On add3, sbo3 and mix3 the free share under the ref library falls by 14-15
  points from its best size (7 or 9) to 11; cmp3d stays at .93-.99 to size 13. No law used up the rule budget and none went
  unproved.
- **The rules' worth grows with size.** The ref library's gain over no rules is 2-14 points at size 7 and 7-37 at
  sizes 11-13 (cmp3d 4, 20, 31, 37 points). The size axis measures what the rules buy, which is what a frontier
  should track.
- **The 50% line is beyond the sizes tried.** Every family stays at or above .78 under its library at size 11 (13 for
  cmp3d), so a threshold frontier needs laws grown three or more times. One salt, one library salt and at most 200
  laws per cell: the per-family steps are a few points to tens of points, so differences under about 5 points are
  noise.

*Does the choice of extras move the frontier? (2026-10-22; run `2026-10-22-draw-band`, 64 s, CPU 42% at launch,
script `draw_band.sh`.)* The size-band laws (salt 11, less every law any draw's salt-1 ref mine mined on, so one set
for all) served under the salt-1 ref library of each draw (0: `gen-warm-fix`, 1-3: `gen-draw1` to `3`). The laws are
the same in every column, so a difference is the libraries'. Free share at size 11 (cmp3d also 13), draws 0 to 3:

| family | draw 0 | draw 1 | draw 2 | draw 3 | best over the mean |
|---|---|---|---|---|---|
| add3 | .795 | .820 | .850 | .835 | +2.5 points |
| sbo3 | .820 | .790 | .810 | .825 | +1.4 |
| mix3 | .775 | .800 | .785 | .785 | +1.4 |
| cmp3d 11 / 13 | .985 / .925 | .985 / .950 | .980 / .925 | .990 / .910 | +0.5 / +2.7 |

- **A few points.** The spread at sizes 9-13 is 1-5.5 points; the best draw beats the mean draw by 0.5-2.7. Having a
  library at all is worth 7-37 points at these sizes (size-band, above), so which extras it was mined on is about a
  tenth of what the library buys. Size 7 (21-184 laws) is noisier: cmp3d .857 against 1.000 is 3 laws of 21.
- So re-targeting the ranker from stream M to the frontier does not open a larger lever: at this n, choosing the
  generator's laws moves stream M by a few percent (above) and the free share by a few points.

*Does the miner's score rank rules by held-out value? Leave-one-out over the ref libraries (2026-10-22; run
`2026-10-22-rule-ablation`, 6 min, CPU 51% at launch; scripts `rule_ablation.sh`, `rule_ablation_stats.py`).* The
falsifier for rewarding a rule by its gain on held-out laws under shift (the frontier's signal) instead of in-sample:
if the miner's ranking already agrees with held-out value, that reward changes nothing. Each family's salt-1 ref library
(`gen-warm-fix`, mon_1) is served whole and less one rule at a time, on its own mine laws (in) and on the size-band's
held-out laws of sizes 9 and 11 (held, 400 per family; salt 11). A rule's drop is the free laws lost when it is
removed; its gain is the miner's logged `+N fixed` when it chose it. The whole libraries reproduce the size-band's
counts exactly.

| family | rules | library's held gain (none to whole) | summed held drops | ρ gain~held | ρ in~held | held drop > 0 | removal helps held |
|---|---|---|---|---|---|---|---|
| add3 | 28 | 263 to 350 (+87) | 2 | .28 | .39 | 10 | 2 |
| sbo3 | 21 | 267 to 339 (+72) | 17 | .58 | .61 | 8 | 2 |
| mix3 | 19 | 288 to 323 (+35) | 32 | .55 | .45 | 8 | 1 |
| cmp3d | 58 | 290 to 395 (+105) | 9 | .22 | .10 | 6 | 4 |

(ρ is Spearman's, with ties ranked by their mean; ρ gain~in is .41-.71. cmp3d's held set is near its ceiling, 395 of
400, so its ρ says little.)
- **The rankings agree at the top and little below it.** The rule with the largest gain also has the largest held drop
  in sbo3 and cmp3d, and ties for it in add3 (2 laws, with three others). Below it most drops are 0-3 laws with many
  ties, so ρ is noisy, but in-sample and held drops correlate only .10-.61 even on the same counterfactual.
- **Some rules are misjudged by far.** mix3's `add(0, x) -> x` was chosen at +4 and costs 2 in-sample laws when removed,
  but 15 held out: a general identity the mine laws barely need. add3's `sub(x, xor(y, 0)) -> sub(x, y)` was chosen at
  +3, yet removing it raises the free count by 2 in-sample and 10 held out. In all, 9 of 126 rules raise held-out free
  laws when removed (a rule that fires first can lead the join away; not traced).
- **Leave-one-out sees little of a library's value.** Except in mix3, summed held drops (2-17) are a small part of what
  the library adds held out (72-105): rules cover for each other. A held-out reward has to score a rule against the
  rules chosen before it, as the greedy miner does, not one at a time against the rest.
- So rewarding held-out gain is a lever, though not a large one per rule: it would promote general rules the mine laws
  under-use and could prune harmful ones. The cheapest test is a held-out backward pass after a mine (drop a rule if
  the held set does not lose by it), scored on stream M and on a frontier set disjoint from the one that pruned
  (`PARKED.md`, "A held-out backward pass after each mine"; tried below on the frontier: no gain). The shift here is
  law size within each family; the held laws come from the same generator.

*A held-out backward pass, frontier side (2026-10-22; run `2026-10-22-held-prune`, 9 min, CPU 26% at launch; script
`held_prune.sh`; throwaway, no source change).* Each ref library above is pruned in one pass, last-chosen rule first:
a rule goes if the pruning set A (the held-out laws above, sizes 9 and 11) keeps as many free laws without it. Arm
`held` looks at A only; arm `both` also requires the mine's own laws not to lose any. The libraries are then scored on
a set B drawn at salt 21 (sizes 9 and 11, about 400 per family, less every line of A and of the mine's laws). Free laws
(B9 + B11; the mine's laws in brackets):

| family | no rules | whole library | `held` (rules kept) | `both` (rules kept) |
|---|---|---|---|---|
| add3 | 275 (347) | 347 (418), 28 rules | 345 (416), 12 | 345 (419), 15 |
| sbo3 | 274 (313) | 338 (381), 21 | 336 (375), 9 | 337 (381), 13 |
| mix3 | 290 (336) | 311 (358), 19 | 306 (352), 9 | 311 (358), 14 |
| cmp3d | 293 (507) | 390 (775), 58 | 386 (768), 16 | 384 (775), 18 |

- **Pruning does not raise the frontier.** It gained at most 2 laws on A, the set it pruned on, and none on B, where
  the pruned libraries are 0-6 laws below the whole ones.
- **But a third to three quarters of each library carries all its value.** `both` keeps 13-18 rules of 19-58 (cmp3d
  18 of 58) with no in-sample loss and B within 0-6 laws. The rest are covered by other rules on these laws. Whether
  the stream's later laws need them (M) was not measured: it needs loops served by the pruned libraries.

*Why a sound rule costs the join: the visit budget (2026-10-22; runs `2026-10-22-join-visit-2`, 41 s, CPU 32% at
launch, superseding `-join-visit`, whose search columns were misread; script `join_visit_trace.sh`).* Removing add3's
`sub(x, xor(y, 0)) -> sub(x, y)` frees 10 held-out laws (leave-one-out, above). None of the 10 has an `xor(_, 0)`;
they are laws the join meets at a larger budget. Free laws on the held-out sizes 9 and 11 (400 per family) by
`JOIN_VISIT`:

| library | 1000 (default) | 5000 | 20000 |
|---|---|---|---|
| add3 | 350 | 377 | 383 |
| add3 without the rule | 360 | 380 | 383 |
| sbo3 | 339 | 348 | 348 |
| mix3 | 323 | 334 | 337 |
| cmp3d | 395 | 397 | 397 |

- **The rule's cost is search breadth.** `join_eqs` adds every rule backward too, and `join_usable` admits this one:
  `sub(x, y) -> sub(x, xor(y, 0))` applies at every `sub` node and adds one node, inside the cap of the larger side
  plus 2. With it the add3 searches reach 391 terms each on average against 355 without it, and 12 fewer meet within
  the 1000 budget. At 20000 the gap is gone. So a rule that pays forward (it normalises) can cost more backward. The
  per-node count is from the code; the share of the extra terms from this rule's backward steps was not counted.
- **The budget is a frontier lever of its own.** 5000 instead of 1000 frees 2-27 more laws per family at sizes 9-11
  (add3 +27, as much as a third of what its library adds), at 1.8 times the reached terms in add3. At the stream's
  sizes, 5000 left only a few laws fewer to the machine proof for 2-3 times the sweep time ("The bounded join removes
  the floor"). So the frontier's definition has to fix the budget, and a cheaper wider search would move it.

*Ordering the join by term size (2026-10-22; runs `2026-10-22-join-order-2` and `-join-order-b`, 2 and 1 min, CPU 31%
and 21% at launch; `-join-order` was the first patch's subset, same counts; probe
`docs/runs/2026-10-22/patches/join_size_first.patch` on 93c148a, reverted; script `join_order.sh`).* Can a search order
buy what the larger budget buys, without the budget? The patch keeps a heap per side and expands one term at a time:
`JOIN_SIZE_FIRST=1` takes the smallest reached term, `=2` the least depth plus size (a growing step costs 2, a
same-size step 1, a shrinking one 0); off, the search is unchanged. Depth plus size was chosen after seeing size-first
on A, so B (salt 21, disjoint from A and the mine's laws; "A held-out backward pass, frontier side") is its check. Free
laws at `JOIN_VISIT` 1000, add3 / sbo3 / mix3 / cmp3d:

| order | A (held-out, salt 11) | B (held-out, salt 21) | mine's own laws |
|---|---|---|---|
| breadth-first (then) | 350 / 339 / 323 / 395 = 1407 | 347 / 338 / 311 / 390 = 1386 | 418 / 381 / 358 / 775 |
| size-first | 363 / 335 / 312 / 397 = 1407 | 354 / 338 / 301 / 388 = 1381 | 419 / 376 / 357 / 773 |
| depth plus size | 360 / 338 / 322 / 396 = 1416 | 354 / 340 / 312 / 388 = 1394 | 419 / 380 / 358 / 773 |
| breadth-first at 5000 | 377 / 348 / 334 / 397 = 1456 | 378 / 351 / 327 / 390 = 1446 | 420 / 381 / 359 / 775 |

- **Size-first trades families.** It frees 13 more add3 laws on A but loses 11 in mix3 and 4 in sbo3, net 0 on A and
  -5 on B. A guess, not traced: mix3's joins need growing steps that size-first defers behind same-size rewrites
  (commutativity and associativity of and, or and xor).
- **Depth plus size is a small, steady gain.** +9 on A and +8 on B (add3 +10 and +7; the others -2 to +2), -2 on the
  mine's own laws, with 12-34% fewer terms reached on A and 14-30% on B (searches meet sooner). At 5000 it adds 4-5 to
  breadth-first's count on both sets. It buys 13-18% of what raising the budget to 5000 buys (+49 on A, +60 on B).
- **Neither order removes add3's rule 4's cost in general.** Without the rule add3 frees 10 more laws breadth-first and
  5 more with either order on A, but 7 more breadth-first and 9 more with either order on B.
- So ordering is not the budget's substitute. Depth plus size is a candidate refinement of the join (fewer terms, a
  few more laws). Keeping it needed its stream M and loop seconds on a sweep, since wall time here was within noise at
  21-52% CPU load; the sweep is in the next section.

*Depth plus size on the sweep; dropping backward steps (2026-10-22; runs `2026-10-22-jsf-sweep-0` and `-jsf-sweep-2`,
34 and 19 min, CPU 22% and 62% at launch, another session's rustc on about 7 cores and a game during the first;
`-join-back-1` and `-join-back-2`, 2 min each, CPU 24-25%; probe `docs/runs/2026-10-22/patches/join_probe.patch` on
a3b1a4e, `join_size_first.patch` plus a `JOIN_BACK` switch in `join_eqs`, reverted; scripts `gen_warm.sh` with
`ARMS=on_on`, salts 1-10, and `join_order.sh` at `JOIN_VISIT` 1000).*
- **Depth plus size lowers stream M and costs less.** Breadth-first on the probe exe reproduces `-gen-warm-fix`'s on_on
  exactly (warm M 754, of it the mined batches 69; cold M 1475, mined 32), so the comparison is like for like. Depth
  plus size (`JOIN_SIZE_FIRST=2`): warm M 732 (mixed 36 to 19, pooled 8 to 3, own and cross unchanged), mined 57; cold
  M 1475, unchanged; the ref mines' M (u3 only) 1 with the generator and 0 without, against 1 and 1. Job CPU: the loops 6460 to 4082 s (-37%), the ref
  mines 1397 to 992 s (-29%), in line with the 12-34% fewer terms reached per search above. Loop seconds fell 1240 to
  451 (warm) and 1409 to 760 (cold), but the breadth-first arm ran beside other sessions' load, so wall time is not
  claimed; job CPU is less exposed to it, not immune (SMT siblings, cache). Rule counts move a few percent (cross 11527
  to 11152; cmp3d's ablated ref mine 291 to 185).
- **Dropping backward steps by shape loses far more than rule 4 costs.** `JOIN_BACK=1` drops a rule's backward step
  when its pattern is one operator over two distinct variables (it matches every node of that operator): mined rules
  (add3 2, among them rule 4; sbo3 2; mix3 1; cmp3d 1) and five promoted ones (`-> add(x, y)` twice, `-> lt(y, x)`
  twice, `-> sub(y, x)`). `=2` drops every backward step that grows the term. Free laws, breadth-first (depth plus size
  within 9):

| backward steps | A (held-out) | B (held-out) | mine's own laws |
|---|---|---|---|
| all (now) | 1407 | 1386 | 1932 |
| none onto `op(x, y)` | 1169 | 1181 | 1660 |
| none that grow | 1044 | 1047 | 1561 |

  With `=1` add3 frees as many laws with rule 4 as without (282 and 281 on A), so its cost is gone, but add3 itself
  loses 68 (350 to 282). The joins need backward steps; which ones cannot be read off a rule's shape.
- So depth plus size is a better join order on every count measured (held-out free laws, stream M, job CPU), and
  rule 4's cost stays with the budget. It replaced breadth-first as the join's only order (`join_search`, the commit
  after 45afcbe): one heap per side by depth plus size, earliest reached first among equals; it frees and reaches the
  same as the probe's `JOIN_SIZE_FIRST=2` on all 15 held-out cells (run `2026-10-22-join-ds-check-3`).

*The visit budget a law needs, by its size (2026-10-22; run `2026-10-22-join-budget`, 2 min, CPU 43% at launch; exe
e0c7b58, depth plus size; script `docs/runs/2026-10-22/scripts/join_budget.sh`).* Each family's salt-1 ref library
serves the size-band's held-out laws (salt 11) one size at a time at `JOIN_VISIT` 250 to 20000. The budget at which free
laws reach their count at 20000:

| family | size 7 | size 9 | size 11 | size 13 |
|---|---|---|---|---|
| add3 | 250 | 5000 | 20000 | |
| sbo3 | 500 | 5000 | 5000 | |
| mix3 | 500 | 20000 | still rising at 20000 | |
| cmp3d | 250 | 1000 | 2000 | 5000 |

- **The budget a law needs grows about twofold per node.** From 1000 to 20000 size 7 gains nothing, size 9 0-7 laws per
  family (of 200), size 11 1-16, cmp3d's size 13 5; 55 of 2589 in all. A fixed budget therefore under-serves exactly the
  larger laws the frontier (the v0.5.0 tag) compares.
- **Serving does not cost more with a larger budget.** Terms reached grow about threefold (add3 size 11: 48063 to
  146479), but serve wall time stays flat or falls (1319 to 1114 ms; cmp3d size 13 3803 to 3018 ms): each law joined is
  a machine proof saved. The cost seen before (5000 at 2-3 times the sweep time, "The bounded join removes the floor")
  was the mines' failed searches under breadth-first, not measured with depth plus size.

*A budget relative to law size: serving gains, mining can't afford it (2026-10-22; runs `2026-10-22-join-budget-rel`,
`-rel-sweep-2000`; exe aa07033 plus `docs/runs/2026-10-22/patches/join_visit_rel.patch`, reverted).* The probe set the
budget to `JOIN_VISIT` at cap 11 (`JOIN_VISIT_AT`), doubling per node of cap and halving below, capped at 2^17.
- **Serving: base 2000 matches a fixed 20000.** Every held-out cell above is within 0-2 free laws of fixed 20000 (base
  4000 within 1). Base 1000 under-serves small normal forms (sbo3 size 9: 169 vs 174 at fixed 1000), since halving
  below cap 11 cuts the budget the smaller laws had.
- **Mining: 3-12 times the job CPU, M no lower.** On the depth-plus-size sweep (`on_on`, salts 1-10) the relative budget
  ran 8 of 30 sweeps before it was stopped: salt 2's `on_on` took 6406 s of job CPU against 526 s at fixed 1000
  (`-jsf-sweep-2`), and salt 1's cross M was 71 against 69. The mines' joins are over candidate rules, whose larger
  sides get the doubled budget, and most of them fail.
- Reverted: the join keeps a fixed `JOIN_VISIT` 1000. A budget for serving apart from mining is parked (`PARKED.md`,
  "The join's breadth").

*What the join can't reach (2026-10-22; run `2026-10-22-join-residue`, 14 s, CPU 16% at launch; exe dabc018 plus
`docs/runs/2026-10-22/patches/join_cap.patch`, env `JOIN_CAP`, reverted; script
`docs/runs/2026-10-22/scripts/join_residue.sh`).* Of add3's 200 size-11 held-out laws, 15 still need a machine proof at
`JOIN_VISIT` 20000 with the salt-1 ref library. Served again:

| arm (on the 15) | budget | cap over the larger side | free | terms reached |
|---|---|---|---|---|
| ref library | 20000 | +2 | 0 | 86499 |
| ref library | 2^17 | +2 (+3 the same: sizes are odd) | 0 | 140942 |
| ref library | 2^17 | +4 (+5 the same) | 2 | 1123792 |
| the four families' ref libraries pooled | 20000 | +2 | 3 | 126807 |
| pooled | 2^17 | +4 | 5 | 1111417 |
| ref + and-idempotence (3 rules) | 20000 | +2 | 4 | 92617 |
| ref + bridges (4 rules) | 20000 | +2 | 5 | 20786 |
| ref + both | 20000 | +2 | 9 | 27426 |

- **Not budget.** At 2^17 every search runs out of terms under its cap (about 9.4k each), not out of budget. A cap of +4
  frees 2 for 8 times the terms.
- **Missing rules.** Idempotence is `and(x, and(y, x)) -> and(x, y)`, `and(x, and(x, y)) -> and(x, y)`,
  `and(x, x) -> x`; the bridges are `sub(or(x, y), xor(x, y)) -> and(x, y)`, `sub(or(x, y), and(x, y)) -> xor(x, y)`,
  `add(xor(x, y), and(x, y)) -> or(x, y)`, `add(or(x, y), and(x, y)) -> add(x, y)`. With both, the full size-11 set at
  2000 goes from 177 free to 183 and size 9 stays at 196: they cost nothing elsewhere.
- **The 6 left** need, by eye, a xor of a term with a part of itself as arithmetic: `xor(x, and(y, x)) = x - and(x, y)`,
  `xor(x, and(sub(-1, x), z)) = x + and(sub(-1, x), z)` (disjoint), `xor(y, or(x, y)) = x - and(x, y)`. All are linear
  MBA identities; none is in any library.
- **Why the miner misses them.** Its candidates come from subterms that use add or sub (`miner.rs`, `candidates`), so
  pure-bitwise rules are never proposed. The bridges could be proposed in principle; that they never are, because no
  straggler has the subterm, is a guess, not checked.

