# A monotone join for an exact miner (decided 2026-10-17)

Decision: keep the join's visit cap (`JOIN_VISIT`, 1000 terms) and let the miner keep a met join's plan under added
rules that act off its path (option 1 below), accepting a rare inexactness, measured as none ("Option 1 built"). The user
first chose option 3 (a depth cap per side, so the join is monotone in the rule set); its probe ("Probe result") found
no depth that keeps the visit cap's strength at an acceptable cost, and the user then chose option 1. Monotone caps that
stay adaptive are surveyed and parked ("Survey"). Measurements are in `docs/tier-cycle.md` ("The miner sees the join");
this file keeps the options and the reasoning.

## Context

- `join_eq` (`tests/church_bv/rewrite.rs`) is a bounded bidirectional search over rule steps (both usable directions) and
  AC steps, terms capped at the larger side's size + 2, stopping when the two sides together have reached 1000 terms
  (checked per layer).
- The miner (`search::rule_miner`) was blind to the join: a candidate that acts only inside a law's join did not count as
  touching the law, so its gain was underestimated. The first fix (the "exact miner") records every
  term the join examines in the law's trace (`Fired::Join`), lets `Trace::touched_by` match a candidate's left side on any
  item and its right side on join items, and memoizes joins per pair in `RewriteMemo.joins`.
- A/B over salts 1-10 (run `2026-10-17-join-memo`, old 8d5b29d against the exact miner): M mines 2 to 0, own 13 to 26,
  cold 1568 to 1563, pooled 33 to 36; summed cmp3d mine time 33 to 51 s. At salt 6 the exact cmp3d mine ran about 81000 join
  searches reaching 13.4M terms, 95% met, with about 41000 memo hits (a probe with the cost line added, not recorded;
  option 1's recorded figures are in `docs/tier-cycle.md`); the gain bound skipped 3603 of 15158
  scorings against 2720 of 5434 before. Nearly every candidate touches the large set of terms a join examined, so the
  memo entry is invalidated and the search rerun for each candidate.
- Kernel cost of joined proofs against the machine proofs they replace (run `2026-10-17-join-proof-cost`, 135 served
  cmp3d batches, salts 1-5, join on against `ABLATE=join`): per joined law, build 7.7 against 21.5 ms, check 0.49 against
  0.47 ms, 965 against 889 unique nodes. A first probe (two batches, not recorded) had set joined laws against rules-only
  ones, which is not the alternative.

## Options considered

1. **Keep a met join's plan under added rules, on the visit-capped join.** Re-search failed joins a candidate touches;
   a met plan is dropped only when a rule added or removed acts on its path. Pro: removes most miner searches. Con:
   inexact: more rules can push a search over the visit cap before it meets, so the miner says met where serving fails.
   **Built** (after option 3 failed its probe).
2. **Revert to the join-blind miner, keep the cost reporting.** Pro: fastest; M as good or better in the A/B. Con: the
   known blind spot stays. Not chosen.
3. **Make the join monotone (depth cap per side, no visit cap), then option 1's memo rule.** Pro: the miner and its memo
   become exact with no special case: a pair that meets within the depth cap keeps meeting under any superset of rules,
   and a failed pair can only flip to met when a candidate adds a step at a term its search examined. Con: no bound on
   the terms one search reaches; branching may blow up on some laws; the depth needs a sweep. **Chosen first, then
   dropped:** the probe below found every depth weaker than the visit cap, and depths 3 and up dearer.
4. **Keep the exact miner as built.** Con: 55% more mine time for no M gain. Not chosen.

Options 1 and 3 share the miner side (met plans survive rules added off their path, failed searches re-run on a touch); option 3 adds the change that makes it exact.

## Research (2026-10-17)

- **A size or visit cap makes a search non-monotone in its rules.** egg stops on iteration, node (default 10000) or time
  limits ([egg `Runner`](https://docs.rs/egg/latest/egg/struct.Runner.html)); ego defaults to 30 iterations and 10000
  nodes ([ego](https://ocaml.org/p/ego/0.0.5/doc/Ego/Generic/Make/BuildRunner/index.html)). The Enumo paper reports the
  effect in practice: under Herbie's 8000-node limit, one of their rule sets did slightly worse, which the authors suspect
  is because it explores a larger space and hits the limit sooner; and two rule sets with equal proving power can perform very differently under limits; redundant rules help
  for the same reason ([Pal et al., "Equality saturation theory exploration à la carte"](https://arxiv.org/pdf/2609.14527),
  sections 4.3, 5 and 6.2). Our visit cap is the same kind of limit.
- **Derivability under limits has no settled definition.** Ruler and Enumo test whether a rule set derives a rule by
  running saturation under a timeout, node or iteration bound, and note that proving power under limits is subtle and
  that no standard definition exists ([Enumo](https://arxiv.org/pdf/2609.14527) section 4.3;
  [Ruler](https://arxiv.org/pdf/2108.10436); [derivability poster](https://uwplse.org/ruler/slides/icfp23-derivability-poster.pdf)).
- **Depth-bounded reachability is monotone.** More rules only add edges, so distances only shrink: a pair meeting
  within depth d per side keeps meeting, given a size cap that depends only on the pair (ours: the larger side + 2). This
  is our argument, not a cited result; the nearest analogue is an iteration-limited e-graph with no node limit. egglog
  gives its semantics with an inflationary operator, as for non-monotonic Datalog extensions, to stay compatible with
  egg applications, which can be non-monotonic ([Zhang et al., egglog](https://arxiv.org/pdf/2304.04332), section 4.2).
- **Proof reuse after a rule change.** KeY reuses a cached closed branch only if every rule it used is still available
  ([KeY proof caching](https://key-project.org/docs/user/ProofCaching)); adding lemmas never breaks a proof, removing a
  used rule does. This is the condition for keeping a met plan when the miner's rule set shrinks (`state()` between
  rounds, preference drops).

No source found on bounded bidirectional joinability tests or on keeping a limited search consistent while rules change.

## Plan (for option 3; step 2 not built, superseded by option 1)

1. Probe: the depth at which today's joins meet, and the terms a search reaches with a depth cap of 2 and 3 per side and
   no visit cap, on the salt-1 sweep. Pick the smallest depth that keeps the joins that meet today without a long tail of
   reached terms; if every depth has such a tail, report it before building.
2. Build: the depth-capped join (delete `JOIN_VISIT`), met plans kept in `RewriteMemo.joins` under rule additions and
   dropped when a rule they used is removed, failed entries invalidated by `Trace::touched_by` as now. Then the A/B
   against 8d5b29d over salts 1-10, and the `ABLATE=join` sanity arm.

## Probe result (2026-10-17): no rule-independent cap tried is both cheap and as strong; the decision is reopened

Run `2026-10-17-join-depth` (`docs/runs/2026-10-17/scripts/join_depth.sh`, the exact-miner build plus
`patches/join_depth.patch`, against 0c383d6 and including the uncommitted exact-miner change: `JOIN_DEPTH=<d>` caps each side at d layers with no visit cap, `JOIN_TRACE` logs each search;
salt 1, all stages; CPU 23% at launch, Defender real-time protection off):

| cap | M cold | M own | M pooled | M mines | searches | reached terms | p99 / max reached per search | wall s |
|---|---|---|---|---|---|---|---|---|
| visit 1000 (today) | 155 | 5 | 5 | 0 | 59342 | 6.9M | 1259 / 3820 | 8 |
| depth 2 per side | 332 | 34 | 32 | 5 | 76751 | 3.1M | 159 / 739 | 6 |
| depth 3 | 238 | 9 | 14 | 0 | 147831 | 22.5M | 1835 / 23729 | 20 |
| depth 4 | 199 | 14 | 7 | 0 | 77572 | 23.9M | 3379 / 246050 (p99.9 17917) | 31 |

Wall times come from arms run two at a time (visit with depth 2, depth 3 with depth 4), so they compare only roughly.

- Today's joins meet asymmetrically: the visit cap lets the side with the smaller frontier go deep. The commonest
  meeting depths are 2+2 (22% of met searches), but the deeper side reaches 5 or more in 13% of them, up to 14. A
  per-side depth cap cuts those; raising it to reach them lets the wide side blow up (depth 4: one search reached
  246050 terms).
- Exhaustive search under the size cap alone (`JOIN_SLACK=0|1` in `join_depth.patch`, salt 6 `mines:cmp3d`, a probe
  not recorded): both arms ran past a 240 s timeout; one search reached 4.4M terms.
- So option 3 as stated fails: every depth is weaker in M than the visit cap, and depth 3 and up also costs more.
  Monotone caps not yet tried: a total depth over both sides, or a depth cap adapted per pair from rule-independent
  data. Option 1 (the visit cap, keeping met plans under added rules) remains, with its error rate unmeasured.

## Option 1 built (2026-10-17)

Chosen by the user after the probe. A failed join still traces every term it examined (exact: it can only flip to met
through a step at one of them). A met join traces only the terms on its path and their subterms, so it is dropped when
a rule added or removed matches one of them, and kept when the added rules act only elsewhere. Results
(`docs/tier-cycle.md`, "The miner sees the join"): over salts 1-10 the miner picks exactly the rules the exact miner
picks, in 46 s of mining against 51; re-searching every kept met plan at each memo hit (`JOIN_CHECK`) found no plan that
failed, in at least 230000 hits. The
inexactness is real in principle and unseen in practice; the survey below is parked until it shows.

## Survey: monotone caps that stay adaptive (2026-10-17, parked)

A Sonnet subagent searched for prior art. It found none on bounding a joinability search monotonically: egg's and
Ruler/Enumo's limits are on search state (iterations, nodes, time); Twee's ground joinability and connectedness tests
use a fixed term order ([Twee](https://research.chalmers.se/en/publication/525501)), but no bound on the search was
found; MM bidirectional search ([Holte et al., AAAI 2016](https://ojs.aaai.org/index.php/AAAI/article/view/10436))
expands neither side past the cost midpoint, which is exact but does not favour lopsided paths. The rest is reasoning,
not sourced:

- The answer is monotone in the rules exactly when the cap is a predicate on a path (or its terms) that does not mention
  the rule set: "some path over the rules' steps satisfies P" can only become true as rules are added. A count of
  visited terms is a predicate on the search state, hence the visit cap's non-monotonicity.
- Candidates, best first: (1) a rule-independent path cost, steps costing by their effect on the term (size-decreasing
  free or nearly, size-increasing 1, AC moves free), with a budget per pair from its sizes: lopsided joins whose long
  side mostly shrinks toward a normal form stay cheap, the idea of ordered rewriting's bounded uphill steps; risk: the
  downhill closure can still be large. (2) Each pair's split of depths frozen by one adaptive search under a fixed
  reference rule set, then searched with those per-side depth caps: monotone, keeps today's choice of which side goes
  deep; risk: the split under the reference rules may not suit later rules. (3) Keep met plans ("a proof stays a
  proof"), which is what was built: not a function of the rule set alone.
- Probes for (1): replay the logged met paths under a few cost functions; count how many of today's joins fit a budget
  that keeps the median search near 1000 terms, and the tail of terms per search. For (2): agreement of the frozen split
  with today's meeting depths, and its tail.

Parked in `PARKED.md`: neither is needed while the visit cap's inexactness stays rare.

Open: whether redundant rules pay under the join's cap, as Enumo found under node limits (a question for the miner's
gain, which scores rules one at a time).

## Survey 2 (2026-10-18): a bound on path cost, split freely between the sides

Asked after the timing one-off (`docs/tier-cycle.md`, "The timing one-off is the join memo's inexactness"). A Sonnet
subagent searched; the two sources below were re-read before writing this.

- **The split between the sides does not change the answer of a cost-bounded search.** GBFHS
  ([Barley et al., SoCS 2018](https://ojs.aaai.org/index.php/SOCS/article/download/18452/18243)) bounds each level by a
  total `fLim` and lets a `split` function divide it between forward and backward limits (never lowering either); "with
  an appropriate split function, GBFHS can search forward, backward, or any bidirectional split", and in unit-cost
  domains, given any order of the sides, it finds optimal solutions on first collision. Choosing a good split
  automatically is listed as future work. fMM and dfMM (Shperberg, Felner, Sturtevant et al.) fix or vary a fraction
  instead; the subagent found no rule for choosing it either (not re-read).
- **Depth-bounded distances only shrink under added edges.** Even-Shiloach trees maintain a shortest-path tree up to
  depth X under edge insertions, each node's distance changing at most X times (Theorem 1.2 of
  [Henzinger, Krinninger, Nanongkai, arXiv 1512.08147](https://ar5iv.labs.arxiv.org/html/1512.08147)): "joined within
  cost C" never reverts as rules are added.
- **Proof orderings as a rule-independent path cost.** Bachmair-Dershowitz-Hsiang order proofs by the multiset of their
  steps' terms, peaks costing most (lecture script, not re-read:
  [MPI autrea 4.6-4.7](https://rg1-teaching.mpi-inf.mpg.de/autrea-ws13/script-4.6-4.7.pdf)); our size cap is the crude
  form of a peak bound.
- No source found for bounded joinability in E, Waldmeister or Twee (they normalize to a fixpoint), for budgeted
  tabling (XSB's incremental tabling keeps fixpoint answers exact under assert and retract), or for any discussion of
  effort budgets (Lean `simp`'s `maxSteps`, our visit cap) being non-monotone.

Reasoning (ours): the visit cap is a bound on search effort; a bound on path cost that depends only on the pair (a
total depth `dF + dB <= D`, or a cost counting size-increasing steps) is monotone, and today's adaptive choice (expand
the smaller frontier) becomes a free split: lopsided joins stay reachable without a per-side cap. The cost moves to
failing pairs, which must exhaust the bound; a safety cap on effort may stay only if it answers "unknown", kept apart
from "fails" in the memo, or the scheduling dependence returns through it. The 2026-10-17 depth probe tried per-side
caps only; a total depth (deep sides up to 14 mean D up to about 16) and the uphill-step cost are untried. Cheapest
falsifier for the uphill cost: log each met path's steps with their size change and side, and count uphill steps per
path; it pays only if nearly all met paths need few (say 4 or under) and the deep sides are mostly downhill. Then
replay the cost-bounded search at that budget for its terms reached per search (p99, max against about 1000), failing
pairs included. The existing `JOIN_TRACE` logs (run `2026-10-17-join-depth`) hold per-side meeting depths, not step
sizes, and predate the lazy join and the extras.

## Probe of survey 2 (2026-10-18): the uphill-step bound is monotone and stronger, but four times dearer

Runs in `docs/runs/2026-10-18/README.md`, salt 1 cold:cmp3d at 2 lanes, a615974's code plus the patches.

- **Met paths need few size-increasing steps** (run `2026-10-18-join-paths`, `patches/join_paths.patch`, every met
  search's path logged with its size changes). Of 1055824 met paths, 87.4% have at most 2 uphill steps and 99.8% at
  most 4; counting flat steps too needs a budget of about 9 for 99%. The deep sides (5 or more steps, 108831 paths) are
  mostly flat steps, not downhill: 3.5 flat, 1.0 down and 1.2 up of 5.7, and at most 2 uphill in 99.4% of them. So the
  falsifier of the survey passed for the cost "uphill steps, flat and downhill free", but the free steps are flat ones,
  the kind whose closures branch.
- **The bounded search beside the real one** (run `2026-10-18-cost-join`, `patches/cost_join.patch`; one pair in 32,
  36920 searches; budget 4, levels raised on the side whose next level is smaller, an effort safety of 200000 terms
  answering "unknown"):

  | real join | shadow met | shadow fail | shadow unknown |
  |---|---|---|---|
  | met (32175) | 32147 | 4 | 24 |
  | failed (4745) | 2947 | 1578 | 220 |

  It meets 99.9% of what the visit cap meets and 62% of what it fails: most of today's failures are pairs with a path of
  few uphill steps that the visit cap stops short of. But it reaches 4.3 times the terms without its unknowns and 8.6
  times with them (stopped at the safety); per search p50 238 against 72 terms, p99 51704 against 1547, p99.9 at the
  safety. Budget 3 is the same but for 14 real joins missed against 4. The shadow makes every term it reaches (the real
  join builds only new terms), so only the reached counts compare, not its time.
- Where the cost goes: a level is closed under its free steps before the other side moves, so even pairs the visit cap
  meets at its first layers pay for the flat closure (met against met: 4.1 times the terms). The 0.66% unknowns are the
  flat closures that do not end.

So a monotone, adaptive bound exists and would also join more laws, but not cheaply. Ways to cut its cost that keep it
monotone, untried: meet checks inside a level (the shadow checks per step only against the other side's closed
levels), flat steps at a fractional cost (between budget 4 and the about 9 that counting them needs), and the free
closure taken modulo AC (a canonical AC form for the flat AC steps, so permutations are one term). The unknowns stay
the open problem: any effort safety must keep "unknown" apart from "fails". Not built; the timing one-off's fix is
still the user's choice (`PARKED.md`).
