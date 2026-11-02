# Parked work

The one list of deferred, parked and unbuilt work (format: `~/.claude/VERSIONING.md`, "Roadmap and parked work"). Each
entry: what, why parked, trigger to reopen, evidence (with the date it was verified), status. The findings themselves
stay in `docs/tier-cycle.md`; this file points into it. Add an item the moment it is parked; delete it when it is built
or fixed, and say so in the doc. Milestones are in `ROADMAP.md`.

Status words: `parked` (deferred; the note says whether it was ever built or tried), `held for <check>` (waits on a named
run or decision), `decided against` (measured and rejected; kept short so it is not retried). Evidence in
`docs/tier-cycle.md` is cited by section or paragraph title, never by line (its lines drift); code by file and symbol.
"Entry below" or "entry above" names another entry of this file.

## Proposer and loop

- **Proposer targets beyond ranking: laws beyond 5 nodes, and new definitions** — why: the floor turned out not to be about size; (c) waits on a way to check conservative definitions. Trigger: (a) when larger laws are shown to teach rules the loops miss: met 2026-10-26, mining fresh laws of the held-out sizes (bands 13-17; the loops serve up to 13) cuts held-out M by up to 28% ("Fresh laws of the held-out sizes do as well"); (c) when conservative definitions can be checked and add expressiveness (the enumerator vocabulary did not pay: "Definitions as an enumerator vocabulary", entry below). Evidence: `docs/tier-cycle.md` ("The proposer model's target: ranking"). Status: (a) held for v0.5, which feeds those laws to the mines as large extras rather than serving them (`ROADMAP.md` v0.5; the two other routes are the entries below); (c) its enumerator form decided against 2026-10-26 (entry below), the rest parked.
- **Mine large laws after the loop (v0.5)** — what: after a loop's last batch, mine fresh laws of the held-out sizes in
  chained batches of 250, as the probe did (-27.7% held-out M at 1000 per band). Why: a second way of feeding the miner
  laws the loop does not serve, beside the extras, which already do that inside each mine; mixed into the mines they
  gain what the dose predicts ("As the loop's extras"). Trigger: the extras fall short of the probe's gain at the same
  count. Evidence: `docs/tier-cycle.md`, "Fresh laws of the held-out sizes do as well" and "As the loop's extras".
  Status: decided against (2026-10-26).
- **Serve laws of the held-out sizes (v0.5)** — what: grow the loops' own sequence 4 times (`STREAM_LEVELS`) so the
  batches hold laws up to size 17. Why: bands 15 and 17 would no longer lie past the loops' sizes, so the frontier
  (the frontier of `v0.5.0`, `git tag -n99 v0.5.0`) would change meaning; loop M would stop comparing with history, and serving large terms costs.
  Trigger: a frontier defined some other way. Evidence: `tests/church_bv/search.rs` (`STREAM_LEVELS`),
  `tests/church_bv/classes.rs` (`HELD_BANDS`). Status: decided against (2026-10-26).
- **A library of mined definitions that outlives the loop** — what: definitions one loop mines are kept and seed later
  loops (DreamCoder-style), instead of each loop mining its own and dropping them at its end. Why parked: by decision
  (2026-10-25, v0.4 design): definitions, one of v0.4's levers, were to be tested per loop
  on the gate's A/B as it stands; a library needs a stored format, a keep-and-forget policy and an order across
  loops, and makes the gate's A/A path-dependent. Trigger: per-loop definitions shown to pay (the enumerator
  vocabulary does not: entry below), and v0.6 (closing the cycle) needs vocabulary to
  compound across iterations. Evidence: `docs/tier-cycle.md`, "They do not transfer"; `ROADMAP.md` v0.6. Status: parked.
- **Defined operators inside `Term`, and normal forms that fold them** — what: (a) a defined operator as a real `Term`
  operator (index 8 and up in a run-time operator table), unfolded at the prover boundary, so rules print and weigh in
  the defined vocabulary; (b) on top of (a), the rewriter folding a definition's body back into its operator, so normal
  forms carry it. Why parked: by decision (2026-10-25, v0.4 design): v0.4 was to build definitions as a vocabulary of the
  enumerators, expanded to base operators as terms are built, since an abbreviation changes no match and reach is
  counted only where enumerators count size (that lever was then decided against: entry
  below). (a) touches six subsystems: the shape and `PatIndex` bit layout
  (`1 << o`, `CLASSES`), `rewrite_uncached`'s per-operator branches (an unknown operator falls into the bitwise one),
  the machine prover (`Machine::step` compiles an operator index of 4 or more as a subtractor, `machine.rs`),
  `witnessed`, `Compiler::ty` and the class table's key header; a missed site misproves silently. (b) adds a fold rule
  per definition and a confluence argument, and pays only for expressiveness, which abbreviations do not add. Trigger:
  (a) when a consumer needs the named form (the GPU model reading rules, or a rule order that should weigh a defined
  operator as 1); (b) when a definition must appear in normal forms. Evidence: operator-site survey, 2026-10-25
  (`tests/church_bv/rewrite.rs` shape bits and `rewrite_uncached`, `machine.rs` `Machine::step`). Status: parked.
- **Definitions as an enumerator vocabulary (v0.4's definitions lever)** — what: definitions the miner's enumerators
  build terms from, expanded to base operators, so a candidate reaches larger terms within the same size caps. Why
  decided against (2026-10-26): an abbreviation adds only reach past the size caps, and that reach does not transfer.
  Mining half of each held-out band at the cross-side cap of 17 nodes instead of 13 cuts the mined half's M 652 to 219
  but the other half's only 1614 to 1610 (of 1951); the transfer is the multi-law rules cap 13 already finds.
  Definitions that add expressiveness (new operators in normal forms, comparisons under `and`/`or`) were not tested
  and stay with their own entries. Trigger: none for abbreviations (a definition that adds expressiveness reopens the
  entries above). Evidence: `docs/tier-cycle.md`, "They do not transfer". Status: decided against.
- **Search alongside execution, and laws uniform in the width (goal D)** — what: proof search running concurrently with execution and fed by what it observes (`../renno`'s gradual checks, effects and run-time hints), and laws proved for every width `n`, not one width at a time. Why: the first was never built; the second was thought to need an induction principle the kernel lacks (§53-57), but `add x 0 = x` and `add x y = add y x` check uniformly in the width on the unchanged kernel as bit streams (`tests/church_bv/uniform_width.rs`, 2026-11-01); the bridge to the fixed-width `Bv_n` also works for `add x 0 = x` (n up to 32, not faster than the per-width proof), the bitwise and `lt` laws bridge too (n up to 32), and `mul x 0 = 0` and `mul x 1 = x` bridge for a literal multiplier (n up to 6; the shift is never exercised by them), `mul x 2 = x + x` bridges too, with the shift observed (n up to 6), and `mul 1 y = y` bridges with a symbolic multiplier (positionwise to n = 7, uniform in the position to n = 9; the end-to-end check of both is super-polynomial, 33.6 s at n = 9, because the kernel converts the statement's `mul(n)` on stuck bits, but a stage-wise bridge at the `Bv` level checks in about n^3, 382 ms at n = 24, and beats the per-width proof from n = 7 or 8 on, 41x in the check at n = 10; one contended run). What stays unbuilt is commutativity, a symbolic multiplicand with a symbolic multiplier, and any law uniform in the multiplier's width (a single fold is ill-typed: no level-lowering map under no cumulativity). Trigger: the belief layer (`ROADMAP.md`, goal 3) wants run-time evidence, or a law has to hold at all widths. Evidence: `docs/superpowers/specs/2026-10-01-search-execution-blend-design.md` (§6 "Open questions", question 4) and `docs/superpowers/specs/2026-10-02-search-execution-blend-design-part2.md` (§53, "Goal D (laws uniform in the width)"), verified 2026-10-24. Status: parked (not built).
- **Port the loop to rings (table refactor, instance builder, metric E)** — why: estimated at 2-3 days; the spike branch `ring-spikes` on origin (8a1df7d) is not merged. Trigger: none stated. Evidence: `docs/tier-cycle.md` ("Ring-theory spikes"). Status: parked.
- **Percentile difficulty band for the proposer** — why: only the fixed band was built. Trigger: none stated. Evidence: `docs/tier-cycle.md` ("Related work"). Status: parked (not built).
- **FunSearch-style collapse control (signature-clustered sampling with a length preference) and AlphaGeometry-style traceback targets** — why: listed as ideas 3 and 4 of "Ideas to take"; not built. Trigger: none stated. Evidence: `docs/tier-cycle.md` ("Related work"). Status: parked (not built).
- **The promoted rules' precedence (tried before run-time rules)** — why: not tested by the promotion-iteration sweep (its other open arm, pooled loops on mix3, went with the families on 2026-10-23). Trigger: none stated. Evidence: `docs/tier-cycle.md` ("Promotion as an iterated sweep"). Status: parked (not tested).
- **Fixed-law weight 100 against 1000 on a held-out `own` loop (phases 1-3)** — why: weight 100 beat 1000 on cmp3d in-sample (serve M 14 against 16) but that is one phase, one salt. Trigger: the held-out loop is "the test"; no result yet. Evidence: `docs/tier-cycle.md` ("The fixed-law weight between 1000 and 0"). Status: parked: the `own` stage was deleted with the families (2026-10-23), so the check would now run on the streams' cold loops.
- **Other ways to build the past-domain held-out set** — what: (a) generate the ablation held-out set at run time from a held-out salt of decision 8's streams instead of frozen files; (b) stratify it per stream (a fixed count from each of the 56) instead of per size band. Why parked: by decision (spec `docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md`, decision 10): (a) would move with any generator change, so ablations at different commits stop being comparable; (b) bitwise-only streams find almost no open laws, so their quota would come from very few. Trigger: (a) when regenerating the files becomes a burden (the key or table size changes often); (b) when the per-band set turns out to miss an operator set an ablation depends on. Evidence: `docs/tier-cycle.md`, "Rotating over every operator pair beats the best pair" (per-pair yields, 2026-10-23). Status: parked.
- **Drop the served laws' twins from the held-out set, not only exact copies** — what: `regenerate_held` drops a law
  salt 1's loops serve only when it is the same pair of terms; a twin (the same law up to renaming or a class-equivalent
  subterm, `canonical`) stays, and a rule mined on it would flatter held-out M. Why parked: changing the filter moves the frozen files
  every ablation compares against, and both arms of an A/B see the same twins. Twins are not few, though: 27% of the
  laws salts 1-10 serve are twins of a held-out law, in every band (2026-10-26, "What the loops see of the held-out
  laws"), so the absolute held-out M and frontier are flattered. Trigger: a held-out M gain an ablation rests on that the
  twins could explain, a claim about the frontier's absolute level, or the next regeneration for another reason
  (dropping twins of the laws the gate's salts 1-10 serve; the extras need no such step, since `scope_extras` drops
  held-out laws and their twins as it draws them, 66a9810). Evidence: `tests/church_bv/classes.rs`
  (`regenerate_held`), run `2026-10-24-held-15-17-2` (`HELD` lines), run `2026-10-26-held-overlap`; phase 2 final
  review M3 (2026-10-23). Status: parked.
- **The extras: count, draw, source and slicing** — what: each loop's mines get extra laws beside the loop's own
  (`scope_extras`, `tests/church_bv/driver.rs`, since 66a9810 on 2026-10-28): from the stream sequence grown as deep as
  the held-out bands (4 growths, every phase and size), the first laws the filter keeps against the served laws and the
  held-out laws and their twins, each mine its own n = `EXTRAS_N` (319) in fresh slices, drawn at the salt (`GEN_DRAW`
  moves the draw). Before it: the first 1650 laws of phase 0 of the 2-growth sequence, n = ⌊0.16 L⌋ in shared slices.
  One entry per knob:
  (a) *Count n.* Held-out M falls about 770 per e-fold of n with no knee, and walk grows about linearly in n, so n is
  a price, not an optimum ("Count and slicing", runs `2026-10-27-xgrid-*`); 319 bought most of the gain at a fraction
  of 9900's CPU (the landing gate: "Count and slicing", run `2026-10-28-land-n319`). The share f (`GEN_F`) went with
  it: n is set directly. Cheaper ways to the same held-out M (2026-10-28, "Cutting a mine short" and "A join budget
  for the mines alone"): a stop rule loses to a smaller n by 460-750 (run `2026-10-28-ladder-f9900h2c`; decided
  against); a lower join budget in the mines alone keeps held-out M down to 100 (5166 against 5340 at 21% of the job
  CPU), and at n 688 gives 4622 at budget 100 and 4577 at 250 against 4690 at 1000 (1247, 1671 and 8870 s of job CPU;
  100's salt 3 ran under heavy load; on every salt its op count is 45-46% of 250's and its walk 26-28%); budget 0 is
  no better than 100, probably worse (5271 against 5166, at the noise; worse on loop M and band 11)
  (runs `2026-10-28-mjv-*`; landed 2026-10-30 as the mines' default at n 319), so it makes larger n cheaper. Trigger: a question resting on the extras' best held-out M, or
  mining made cheaper (met: budget 100 landed). Status: held for a choice of n against mining CPU on the landed budget (n 688 at 100: 4622
  against 5166, at 1247 against 627 s of job CPU on salts 1-3).
  (b) *Draw: a learned ranker choosing which laws each mine takes.* Redrawn lists leave batch 0 and job CPU unchanged,
  and the best of four draws saves 51 of about 2230 M, against 7-37 points of held-out free share for having a library
  at all ("How much choosing the extras can gain", "Does the choice of extras move the frontier?", runs
  `2026-10-22-gen-draw1` to `3`, `-draw-band`). Trigger: a much smaller n, or a vocabulary that makes some laws far
  more useful than others. Status: decided against.
  (c) *Source.* Padding laws lost to the stream (M 40 against 29, worse on 6 salts of 10); the mixed grammar had M 21
  against the non-padding laws' 10 at 9 against 26 times the stream's loop time and was held for a cost limit (runs
  `2026-10-17-gen-wide`, `-gen-round-a`, `docs/runs/2026-10-17/README.md`). No source switch is left in the code: the
  deep stream sequence is the only source (66a9810). Status: decided against (a new source would be a new arm).
  (d) *Shared slices* (a loop's mines mining the same n laws): they beat fresh slices on the families (round A,
  2026-10-18), but on the streams with the deep source distinct laws per loop matter more than laws per mine: fresh
  got 90% of shared's held-out gain at half its CPU at 4950 and 93% at 41% at 9900 ("Count and slicing", runs
  `2026-10-27-xgrid-f4950h`, `-f4950`, `-f9900h2`). Deleted in 66a9810 (`xgrid.patch` in
  `2026-10-27-xgrid-exes` has both). Status: decided against.

- **Learned proposer, stage 2 (the cycle) and richer scorers (v0.6)** — what: refit the scorer each round on the labels of
  earlier rounds; or a richer model (more features, a Rust ML crate, the GPU model) behind
  an offline scorer. The stage 1 scorer, `SCORER`, `select_extras` and `RULEMINER_TRANSFER` were removed on 2026-10-31 (recover with `git show 8d9ceaf^:tests/church_bv/scorer.rs`). Why: stage 1's count-feature scorer found offline signal (test AUC 0.691 vs size-only
  0.528) but no curve shift: held-out M worse than random at n 80/160/319 and 1.1-1.4x the CPU. Trigger: a model that sees a law in context (the other laws of the mine) or a different kind of feature, beating random beyond the redraw spread (sigma 76 held-out M over salts 1-3). Context model, offline only (2026-11-01, `docs/tier-cycle.md`, "A context model over the extras"): at k = 80 it ranks credited laws above the per-law model and `small` (both intervals above 0, 7 of 7 salts), at k = 160 there is no room (every ranker is at the ceiling), so the approved strict Q1 bar reads FAIL and the trigger is not met; the stage-2 gate (Q2) would need its own plan. Evidence: `docs/tier-cycle.md`, "A learned scorer
  over the extras" (runs `2026-10-31-v06-labels`, `v06-g1` to `g6`). The size-blind refit and the w2 transfer label (2026-10-31, runs `v06-g7` to `g12`) were also null: three scorers over count features all lose to random. Status: parked. Straggler-first selection from the mine's own verdicts (the second try, runs `v06h-g1` to `g5`) lowered held-out M at every n but at 1.4-1.9x the CPU, null by the rule; the trigger is a selection or model that beats random at equal CPU (2026-10-31). Selection by the mine's own verdicts did beat equal-work random at n <= 160 (`cheap`, then `small`, 2-4% of about 4800 held-out M, runs `v06k-g1` to `g12` and `v06j3-g1`, `g2`) and is v0.6's answer (`ROADMAP.md`); what stays null is a learned model and a selection that wins at equal CPU past n 160.


- **Cheap selection beyond mined-rule steps (v0.6)** — what: a cap or pool larger than about 4n that keeps mine 1 selective past n 160. Why parked: `small` (steps then normal-form size) fixes the dead key and holds held-out M at 4-15% fewer match/op counts (`v06j3-g1`, `g2`), 1.95% fewer instructions at n 160 salt 1 (`v06j3-icount`, `v06j3-icount-sm`); the crossover is charted (wins n 80-160, loses n 200 and 240, `v06h2-g1` to `g6`) and its cause read from the logs; a better key is a new design with no evidence. Trigger: a decision to use selection in the loop at n above 160, or a key that is nonzero under an empty base. Evidence: `docs/tier-cycle.md`, "The cheap variant" (runs `v06h2-g1` to `g6`, `v06k-g1` to `g12`, 2026-10-31). Status: parked.
- **Credit-guided / coverage-guided extras (c1, a2) (v0.6)** — what: a cross-loop credit file (a2/c2) and any other per-law signal for the pool. Why parked: three per-law signals have now failed to beat `cheap` or random at matched work (the stage-1 scorer, the binary coverage class which equalled `cheap`, the graded reach which lost by 86-88 or was noise); loops do not chain in the sweep, so a2 would also need a new carry path. Decided against for reach-by-served-candidates in both directions. Trigger: a signal that is not a function of one law and the served candidates (for example the marginal gain of a law to the greedy set), with an offline check on one mine's logs first. Evidence: `docs/tier-cycle.md`, "The cheap variant" (runs `v06n-g1` to `g4`, `v06g2-g1` to `g4`, 2026-10-31). Status: parked.
- **Sibling proposer (l3, v0.6)** — what: a proposer that suggests new laws beyond the pool (a model or a second miner), not a selector over a fixed pool. Why parked: v0.6 closed with selection only; every per-law selector signal tried (stage-1 scorer, coverage class, graded reach) failed to beat `small`/`cheap` (`docs/tier-cycle.md`, "Graded reach keys"). Trigger: a pool whose best laws a selector cannot reach, shown by held-out M still rising with pool size at fixed n. Evidence: `docs/tier-cycle.md` sections "Crossover and steps" and "Graded reach keys", 2026-10-31. Status: parked.
- **Marginal extras selection (h1b, v0.6)** — what: pick pool laws by what they add to the mine (for example stragglers whose candidate left side no kept law has yet, or those still uncovered after a first greedy pass over the served stragglers), instead of the first n stragglers. Why parked: straggler-first (h1a) bought held-out M at 1.4-1.9x the CPU of a random draw of the same n, and doubling n was the cheaper route (r638 4600 at 910 s against h319 4498 at 1252 s); h1b targets the same cost only if it cuts mine work, which is not shown. Trigger: a selection that reaches a random arm's held-out M at lower job CPU (the rule in `docs/superpowers/specs/2026-10-31-context-aware-selector-design.md`), or a way to drop the cost of proving the extra stragglers. Evidence: `docs/tier-cycle.md`, "Selecting the extras by straggler verdict" (runs `v06h-smoke`, `v06h-g1` to `g5`, 2026-10-31). Status: parked.

- **Extras selection: test gaps left from the v0.6 review** — what: no test for the driver's `run_loop` env push (`n == pool` and the bad-value panic messages are tested since 2026-10-31). Why parked: the selector is off by default after the null result (`docs/tier-cycle.md`, "Selecting the extras by straggler verdict"); the pool-start miscount (now `read_named_laws(..).len()`) and the config-parse test are fixed. Trigger: a rerun of the selector (h1b). Evidence: final review of 2026-10-31. Status: parked.

## Rewriter, rule order and the floor

- **Learn a rule order (a global order, or a priority per rule)** — why: no better global order was found; the one signal left on the families was per family (sbo3 under size first), and the families are gone (2026-10-23), so a learned order would start from the streams. Trigger: none stated. Evidence: `docs/tier-cycle.md` ("Rule order"), `docs/tier-cycle.md` ("Operand order"); also `docs/learned-vs-fixed.md` ("Moving parts to learned: candidates", the rule-order row). Status: parked.
- **Learn which rule wins at each overlapping pair, or complete overlaps Knuth-Bendix style so order stops mattering** — why: needs a critical-pair finder, or is "most work"; the pooled library had about 1000 critical pairs (overlaps are still found by `rule_overlaps`, `rewrite.rs`). Trigger: none stated. Evidence: `docs/tier-cycle.md` ("Rule order"). Status: parked (joinability units and the critical-pair finder were built, then deleted with the pooled library on 2026-10-23; tag `v0.2.0` has them).
- **On a cycle cut, return a canonical cycle member (for example the `show()`-least term visited)** — why: it would let both sides of 59 of 101 floor laws meet, but the bounded join removed the whole floor, including the 37 cmp3d permutation laws a canonical member would not reach. Trigger: none. Evidence: `docs/tier-cycle.md` ("Completion on the floor"), `docs/tier-cycle.md` ("The bounded join removes the floor"). Status: decided against (superseded by the join). A learned table of class representatives does the canonical job differently: each class's smallest enumerated term, not a cycle member ("A learned table of representatives: the probe"; candidate 4 in `docs/learned-vs-fixed.md`).
- **Cheaper join searches: an early cut of failing searches, and a two-level match index** — what: the two levers left
  of the 2026-10-18 join survey. Why parked: each is bounded. Failed searches were 26% of salt 6's cmp3d mine's search
  time (23-48% in mines with extras), so an early cut saves at most about a quarter (the gain bound saves no time); a
  two-level match index saves at most about 10%. Built from the same survey: the interner's per-thread cache, lazy join
  steps (7ee55b3), the stages' loops in lanes (397dcf2), lock-free interner reads, the size bound before matching and
  the interner's hash tags (8de04c1, 2de4854), and the spine deferral (eabd8d5). The operator-invariant cut fired 0
  times (run `2026-10-18-join-count`), and join memos shared by a loop's two mines run in separate processes: both
  decided against. Trigger: join cost becomes the limit; at 4950 large extras the join is 67% of a sweep's busy samples
  (run `2026-10-26-cu14-d3-prof`). Evidence: `docs/tier-cycle.md`, "The miner sees the join", "The interner's
  per-thread cache", "Where an extras mine's time goes", "Lazy join steps, and sweeps in lanes", "Counts behind those
  levers". Status: parked (not built). The join levers tried and decided against, each exact:
  (a) *the step's whole term made only when expanded* (branch `lazy-view` on origin, a7eccef and 984bde2; patches
  `docs/runs/2026-10-18/patches/lazy_reach.patch` and `lazy_at.patch`, applying on d7cf8b9 in turn): slower than
  `main`, since every comparison walked both derivations (runs `2026-10-18-lview-ab`, `-lview2-ab`; "The three levers,
  tried");
  (b) *a 2-way interner thread cache*: at the same 512 KB, hits 74.0% to 77.5% (4-way 79.7%), most misses capacity
  (runs `2026-10-18-cache-ways`, `2026-10-17-op-cache`);
  (c) *nested join steps inner first* (b7bb853, reverted): more searches met, but the rules it mines cost more; under
  `JoinStep::order`'s guard every order-free trace (canonical, all shortest paths, one canonical path per pair) costs
  more than the skip saves (runs `2026-10-20-inner-gate`, `-guardin-gate`, `-canon-gate`, `-split-exact`,
  `-pair-exact`, `-pair-cost`; "Nested steps inner first only");
  (d) *skipping the step that undoes the one before* (07e3416, dropped): about 4% more job CPU on top of the spine
  deferral (run `2026-10-19-spine-back-quiet`, `docs/runs/2026-10-19/patches/undo_skip.patch`);
  (e) *a repeated-variable pre-check before `match_pat`*: at most 15-28% of the matcher's node visits; `PatIndex::get`'s
  depth-2 pair check replaced it (75d4b99; runs `2026-10-19-rep-var`, `-shallow-eq`, `-pairs-quiet`; "What a
  repeated-variable pre-check would save", "The depth-2 pairs in the index").
- **The miner's serial main thread: evaluate the chosen set in parallel** — `affected` (`TraceIndex` on the scoring threads, run `2026-10-18-aff-index-ab`) and the winner's rivals (through the round's worker queue, `2026-10-18-rivals-pool-ab`) are built, both exact. Before the rivals moved, `state` was 25% of the main thread's samples (`2026-10-18-aff-prof`); evaluating the chosen set in parallel can be exact (surveyed 2026-10-18, not built): every memo entry is a pure function of its key under the round's rules (`rewrite_memo` stores no entry that ran the budget out or cut against a term further out, and debug builds check each replay with `check_replay`; `join_eq` stores `join_search`'s result and the terms it examined, and serves a failed one only while the join store has no path for the pair, 60d8116: the store is then an input too, so a parallel evaluation reads one store), which is what already lets `state` reuse a filtered seed. So give every worker the whole filtered seed, split the laws over the workers, and merge the grown memos by union (two entries for one key are equal); each law's evaluation is then the serial one. It needs the memo's `Rc`s (`PlanRc`, `Rc<Rewritten>`, the join entries' `Rc`) made `Arc` or copied per worker, and the gain is small: `state` was about 3.4 s of a ~100 s sweep. The winner loop's own 12% is the thread parking on results, not work. Why parked: small gain for an `Rc` to `Arc` change across the memo. Trigger: sweep wall matters and a re-profile shows `state` as most of the one-busy-thread wall. Evidence: `docs/tier-cycle.md`, "Where the sweep's wall goes"; `state` in `tests/church_bv/miner.rs`. Status: parked.
- **Serve met joins from the join store only, keeping the memo's join entries for failed searches** — why: the memo's join entries also hold failed searches, a worker's repeats within one candidate (its store copy is read-only) and the main thread's seeds across rounds, so they cannot simply go; only the met entries overlap the store, and how many memo hits they are is not measured. Trigger: a count of memo join hits split by met and failed, and by main thread and worker, shows met hits on pairs the store serves as most of them. Trigger met by count 2026-10-21: 88.1% of memo join hits over cold:cmp3d salts 1, 3, 5 (run `2026-10-21-hit-probe`). The merge still removes no concept: the memo stays for failed pairs (3.5%) and the workers' unserved repeats (8.4%), and a served path can differ from the memo's plan. Evidence: `docs/tier-cycle.md`, "Whether the memo's join entries can go" and "Memo join hits by kind" (2026-10-21); `RewriteMemo::joins` and `join_eq` in `tests/church_bv/rewrite.rs`. Status: held for a decision (counted, not built).
- **A monotone but adaptive cap for the join (a rule-independent path cost with a per-pair budget, or each pair's depth split frozen under a reference rule set)** — why: the miner keeps met plans under added rules, which is inexact where added rules push a search past `JOIN_VISIT`; no kept plan failed in at least 230000 re-searched hits over salts 1-10, and per-side depth caps were weaker and dearer. Trigger: `JOIN_CHECK` (`docs/runs/2026-10-17/patches/join_check.patch`) finds flips, or the miner's and serving's views of the join disagree. Trigger met 2026-10-18: with extras on, `JOIN_CHECK` finds flips (up to 65 per lane worker in salt 1's cold:cmp3d loops, run `2026-10-18-join-check`), and the inexactness makes the miner's choices depend on scheduling (fixed 2026-10-18 by scoring each candidate from an empty memo, `docs/tier-cycle.md`, "Fixed by a memo per candidate"). Evidence: `docs/decisions/2026-10-17-monotone-join.md` ("Probe result", "Survey", "Survey 2" and "Probe of survey 2", 2026-10-18: a bound of 4 size-increasing steps with a free split between the sides is monotone and meets 99.9% of the visit cap's joins and 62% of its failures, at 4.3-8.6 times the terms reached, 0.66% unknown at a 200000-term safety; modulo AC it costs 1.8 times but loses 21% of the joins; in the miner it ran out of memory at 34 GB; in serving only it changed no loop's M on salts 1-3, and serving's join failures are exhausted small pairs, none at the cap). Status: parked (not built; per-side depth caps 2-4 decided against; the scheduling dependence it was to fix is fixed otherwise, so its remaining use is joining more of the miner's pairs, at 4-9 times the terms).
- **Whether redundant rules pay under the join's cap** — why: Enumo found redundant rules help under node limits; the miner scores rules one at a time, so it values a redundant rule at 0. Trigger: a miner that scores rule pairs, or join failures at the cap that a redundant rule would avoid. Evidence: `docs/decisions/2026-10-17-monotone-join.md` ("Survey: monotone caps that stay adaptive", its closing "Open" line). Status: parked (not tried).
- **A held-out backward pass after each mine: the stream-M arm** — what: after a mine, drop each chosen rule whose removal costs no free laws on a held-out set of larger generated laws (and none of the mine's own), then run the loops on the pruned libraries and compare stream M and loop seconds. Why parked: its frontier side was tried and gains nothing (a disjoint set's free laws move 0 to -6 per family), so only M or cost could pay; the pruned libraries keep 13-18 of 19-58 rules, so the join has fewer backward steps and could be cheaper. Trigger: loop cost becoming the target, or a reason to want smaller libraries (a vocabulary, goal 2 in `ROADMAP.md`). Evidence: `docs/tier-cycle.md`, "Does the miner's score rank rules by held-out value?" and "A held-out backward pass, frontier side" (runs `2026-10-22-rule-ablation`, `-held-prune`, verified 2026-10-22). Status: parked (M arm not tried).
- **The join's breadth: backward steps of normalising rules, and the visit budget** — what: every rule also joins backward (`join_eqs`), so a sound normalising rule such as `sub(x, xor(y, 0)) -> sub(x, y)` read backward applies at every `sub` node and spends the 1000-term budget (`JOIN_VISIT`) sooner: with it, 10 fewer of add3's 400 held-out laws are free; at budget 20000 the gap is gone. The budget alone moves held-out free laws by 2-27 per family from 1000 to 5000. Ordering tried (probes, reverted): size-first trades families; depth plus size is better on every count measured (held-out free laws, stream M, job CPU), is now the join's order, and does not remove rule 4's cost (see "Depth plus size on the sweep"). Dropping backward steps by a rule's shape: decided against (the joins lose 205-371 free laws per set). A budget relative to law size (doubling per node from 2000 at cap 11) serves held-out laws as well as a fixed 20000 but costs the mines 3-12 times the job CPU with M no lower (reverted, "A budget relative to law size"). Left: serving wants more budget than mining can afford, so a separate serving budget. Its converse half was measured 2026-10-28: budgets of 500 down to 100 in the mines alone, serving and the held-out check at 1000, keep held-out M (5166 against 5340 at 100) at 21% of the job CPU; budget 0 (no join in the mines) is no better than 100 and probably worse (loop M, band 11), and 100 at n 688 is level with 250 there at 45% of its op count (56% of its job CPU on salts 1-2; salt 3 ran under heavy load) (`docs/tier-cycle.md`, "A join budget for the mines alone", runs `2026-10-28-mjv-*`). Why parked: the stream's M does not move; only held-out serving gains (55 of 2589 laws from 1000 to 20000). Trigger: the frontier (ROADMAP v0.5) as the score, where larger laws make the budget matter, or join cost becoming the target. Evidence: `docs/tier-cycle.md`, "Why a sound rule costs the join: the visit budget" and "Ordering the join by term size", "Depth plus size on the sweep; dropping backward steps" (runs `2026-10-22-join-visit-2`, `-join-order-2`, `-join-order-b`, `-jsf-sweep-0`, `-jsf-sweep-2`, `-join-back-1`, `-join-back-2`, `-join-budget`, `-join-budget-rel`, `-rel-sweep-2000`, verified 2026-10-22). Status: decided 2026-10-30: 100 at n 319 (n 688 costs 1.45x the base's job CPU for 8.5 more points of held-out M); landed as the default 2026-10-30 (gate `2026-10-30-land-mine100`: held-out M 5166 against 5340 at 22% of the job CPU).
- **One rule per left side within a mine (drop, or replace on a second)** — what: `RULEMINER_NODUPLHS` drops candidates whose left side has a base rule, but a mine may still choose a second right side for a left side it chose this mine (a rival's sibling stays a candidate). Either drop such candidates or let the second replace the first. Why: 30 of gen-warm-fix's 2320 mines did it (24 at +0 fixed, a size gain, mostly `add(0, x) -> xor(0, x)` then `-> x`; 6 at +1), so dropping them would lose real gains. In all 6 +1 cases the second rule's right side sorts first in `run_order`, so it shadows the first in rewriting and the first only gives join steps. Serving each loop's later batches without the shadowed rule changes M in none of 12 batches (join reach -1.7% to +1.5%). So replacing would cost nothing measured and gain only tidier libraries, at the price of a swap move in `pick`. The exact-duplicate guard (`by_bound`, `best_rival`) closes the hang route either way. Trigger: library size or readability matters, say a proposer trains on mined libraries. Evidence: run `2026-10-22-gen-warm-fix`, mine logs and an A/B of `search::rule_set_kernel_check` (2026-10-22). Status: decided against.
- **Runner-up lookahead failed on sweeps; why is a guess** — why: it changed nothing on the cmp3d loop and lost on most sweeps; the explanation (a runner-up is a different rule) is untested. Trigger: none. Evidence: `docs/tier-cycle.md` ("Lookahead over runners-up too (negative, removed)"). Status: decided against (its explanation untested).
- **Derivability prune on the mined library (Ruler/Enumo style)** — why: tried, negative. Trigger: none. Evidence: `docs/tier-cycle.md` ("Derivability prune (negative, 2026-10-10)"). Status: decided against.

## Proof shapes and compiled evaluation

- **One tree per side for all of a law's `F_j`** — why: saves only the splits, at most about 7% of reduction work (about 1.3-2.6% of a sweep), before the conjunction leaves' own checking cost. Trigger: "unless the split cost grows" / a new proof shape. Evidence: `docs/tier-cycle.md` ("Leaves stated evaluated, or one tree per side: neither pays"). Status: parked.
- **Delayed substitution (suspended instantiation in the kernel)** — why: bound of about 20% of busy samples counted generously, about 5% counting new nodes only, before losses; adds a trusted constructor every reader must force. Trigger: a probe weighting each `inst_rec` result by the work below it shows over about 15% of busy samples never read by the checker in the same scope; then prototype behind a feature with `kernel_soundness_fuzz` and the scoped `instantiate_n` test. Evidence: `docs/tier-cycle.md` ("Design note: delayed substitution"). Status: held for its probe gate.
- **Reopening the kernel speed-up thread** — why: every work-avoiding lead was measured and closed; 72% of reduction work under `conv` is gate terms on concrete bits. Trigger: a new proof shape (fewer leaves, for example a symbolic per-gate lemma in place of `lemma_n`'s 2^k trees) or a cheaper evaluator. Evidence: `docs/tier-cycle.md` ("Kernel speed-up thread: closed"). Status: parked.
- **Head-first `conv` shortcut; substituting a spine's arguments at once** — why: same-head pairs carry 7% of the reduction work and the argument checks cost 1.17 M visits to save 0.20 M; the spine case is a small part of the 8.4%. Trigger: none. Evidence: `docs/tier-cycle.md` ("What `conv` reduces, and the type checker's own substitution"). Status: decided against.
- **The formalised Wasm target machine's remaining obligations over Church bit-vectors** — what: the `add`/`sub`/`mul` laws not yet proved (associativity, `sub x x = 0`), `lt_u`/`gt_u`/`le_u` as circuits with their lemmas, closure packing (P1/P2), the allocator and 32-bit arithmetic, memory read-over-write, and the memory-size questions (4 GiB, `memory.grow`). Why: by decision, "consumers decide the next lemma; no speculative circuit library" (§90); D3, D1, D2, H3, `good_add` and H4 are built (`tests/church_bv/encoding.rs`). Trigger: a consumer (the target machine's statement, or a JIT lowering) needs one of them. Evidence: `docs/superpowers/specs/2026-09-30-bitvector-interface-design.md` §8 ("Open questions") and §90 ("H1 direction: laws over circuits"), verified 2026-10-24. Status: parked.
- **Compile hot transformations, with learned compilations (lowering rules mined by target cost)** — why: not built; the base was probed twice (lowering templates are provable as kernel laws; M-scored and size-scored mining pick different rules), and the mined rules do not fire on the JIT's programs (option A's result, 2026-10-17). Goals 1 and 2 of `ROADMAP.md` meet here; `README.md`, "Future work", has the summary. Trigger: workloads with arithmetic depth (the specialiser does not produce it by inlining on the corpus, 2026-11-01), and a bridge from the loop's width-n laws to the JIT's i64 (`PARKED.md`, goal D). Evidence: `docs/tier-cycle.md` ("Compiling hot transformations, with learnable compilations"; "Other ways to join the JIT and the loop"). Status: parked (not built).
- **Native ISA semantics below wasm (option D: Sail models of Arm-A and RISC-V)** — why: ISA models are large and the native code is Cranelift's; Crocus already verifies Cranelift's lowering rules, so this is not a part to rebuild. Trigger: none stated. Evidence: `docs/tier-cycle.md` ("Formalizing the target machine"). Status: parked.
- **Closure specialisation's V1 and C: hoisting loop invariants (`Step::HoistInvariant`) and a kernel proof built from the specialiser's trace, then policy tuning** — why: only V3 was planned and built (b03dc96 ... a873411, plan `2026-09-24-closure-specialisation.md`); C is sized like the core of `prove_tail_recursive_universal`, and V1 must relate `Ev` families of different arities. Trigger: a JIT program whose specialised form has to be kernel-proved equal to its source (goal 1), or benches showing the specialiser's policy costs. Evidence: `docs/superpowers/specs/2026-09-24-closure-specialisation-design.md` ("Open questions and future work"), verified 2026-10-24. Status: parked (not built).
- **Strict against lazy evaluation in the closure specialiser** — why: lazy evaluation changes what programs mean, touches every layer and costs thunks on numeric loops. Trigger: when C (a kernel builder that consumes the trace) starts, or if the corpus gains terms with expensive unused arguments. Evidence: `docs/superpowers/specs/2026-09-24-closure-specialisation-design.md` ("Open questions and future work"). Status: parked.
- **A prover that knows what `shr1` means** (a right-shift-aware carry encoding: `Machine::parse` refuses `shr1`, since a
  right shift reads a later position) — the end state of the class table's representative choice (spec
  `docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md`, decision 7). Why parked: its own project; the
  table's parse-first representatives already prove every held-out replacement. Trigger: the table's serve logs report
  unusable `shr1` replacements that cost laws (about 12% of sampled `shr1` merges are unusable). Evidence:
  `docs/tier-cycle.md`, "`shr1` in the class table, its proofs over atoms, and a table's memory" (2026-10-23).
  Second symptom, 2026-10-25: 355 of the 386 stragglers the miner leaves uncovered over the baseline's 30 loops are
  laws the rewriter never closes, and every one has `shr1` (`docs/tier-cycle.md`, "Where a loop's definitions should
  come from"; run `2026-10-25-uncovered`). Its size, 2026-10-25: with an oracle admitting every true `shr1` rule the
  miner proposes, M falls only 1718 to 1620 (run `2026-10-25-shr1-oracle`, same section), so a prover alone is worth
  about 100 of M; batch 0's share is out of any rule's reach, and the rest are laws first seen at serve, which the
  miner closes once seen (run `2026-10-25-why-uncovered`, same section). At the loops' width (4) a general
  every-input proof already proves all 219 oracle `shr1` rules, 0.4 s each over three variables (spike 2026-10-26,
  same section, "At the loops' width"), so a `shr1` encoding is needed only beyond width 4. Since 2026-10-26
  `prove_rule` falls back to that proof for rules of at most 12 input bits (ab6f4a7, held-out M -8.7%, same section,
  "Kept: the every-input fallback"); what stays parked is a `shr1` encoding for rules over 12 input bits and for widths
  past 4 (the JIT's). Trigger now: `shr1` rules over 12 input bits that the miner proposes and cannot prove cost M, or
  a JIT program needs a `shr1` proof past width 4 (not met 2026-10-26: one winner in 60 mines, same section, "What it
  leaves unproved"). Status: parked (by decision, 2026-10-23); its width-4 part done 2026-10-26.
- **The every-input proof as the only rule prover** (`prove_rule` would keep `every_input_law` alone and delete its other
  routes: the bitwise case split, `shr_not_law`, the `shr1`-root rewriting, the carry encoding) — why parked: by
  decision, 2026-10-26, on cost: about 0.4 s a rule at 12 input bits against about 87 ms for a winner's proof on cmp3d (`miner.rs`, `play`), and
  16x per 4 bits more, so rules over 13 input bits or more (4 variables at width 4) still need the old routes, which
  splits the prover by size anyway. Trigger: the every-input proof's cost comes within about 2x of the routes' at
  16 input bits (a cheaper case split or kernel evaluation), or a gate shows the old routes prove nothing the
  fallback could not. Evidence: `docs/tier-cycle.md`, "At the loops' width, every-input proofs" and "Kept: the
  every-input fallback" (2026-10-26);
  `rewrite.rs`, `prove_rule`. Status: parked.
- **Boolean combinations of comparisons (`lt` results under `and`/`or`/`not`)** — why: machine side is cheap (spike passed) but the gain is capped at about 17% of M in the head start and the rule side is untouched. Trigger: the cmp3d library becomes the limiting factor, or the kernel extending its own vocabulary (goal 2, `ROADMAP.md`; its enumerator form was decided against: "Definitions as an enumerator vocabulary", under "Proposer and loop"); restart from the spike patch and a half-day `prove_rule` probe. Evidence: `docs/superpowers/specs/2026-10-09-boolean-comparisons-spec.md`, "Spike result (2026-10-09): PASSED". Status: parked.

## Kernel memos, footprint and allocation

- **Kernel memo, walk and arena levers: each within noise or worth about 1-3.5%** — what: the levers left from the
  kernel speed-up and id-arena work, each measured or bounded small. Why parked: none is worth its code or its trusted
  surface at its size. Trigger: a profile of the kernel check showing the cost the lever removes (each item's own
  trigger, where it has one); the kernel check was 4.4% of a streams sweep's busy samples (run
  `2026-10-26-cu14-base-prof`). Evidence: `docs/tier-cycle.md`, each item's paragraph. Status: per item.
  (a) *Shared node id with an immediate leaf value, and per-table height cutoffs*: leaf cutoffs for the infer, shift
  and instantiation memos within noise (82.2 against 81.6 s; "Leaves skip the infer and shift memos (negative,
  2026-10-13)"). Decided against.
  (b) *Low-node cutoff for the other memos*: removes 3% of `shifts` entries and under 1% of the others, which hit 81-83%
  against 43% overall ("Memo census of rule 33's check"). Decided against.
  (c) *Closed-term normal-form cache across calls*: at most about 70 ms of 6.76 s (1%), and it adds to the trusted
  kernel ("A closed-term normal-form cache would save about 1% (negative, 2026-10-13)"). Decided against.
  (d) *Skip `inst_get` for argument-list ids with no entry yet*: at most about 1.4% of busy samples, too small for the
  per-id flag it needs ("Who looks up what, and how much a one-entry slot per node would catch"). Parked.
  (e) *`uses` before `inst_get` in `inst_rec`'s `go`*: never A/B'd in this order; at most 1-2%, and a swap may lose,
  since a one-entry slot answers 82% of `uses` lookups ("Survey: the lever after the trace filter"). Parked (not
  built).
  (f) *Canonical handles end to end* (a builder-interface change across `tests/church_bv`): at most about 3.5%, less in
  practice ("How many builder inputs the caller already holds"). Parked.
  (g) *Walk or memo chosen by term size*: a size threshold, not a general mechanism; the slot's misses alone cost +5% on
  small terms ("The shared memo in the real kernel: negative"). Parked (not tried).
  (h) *Smaller bytes per node* (merged memos, dropping the stored hash): the maps hold about 30 B used and 54 B
  allocated per node, and the cheap levers are worth about 3% ("The hash maps' load and entry size"). Parked.
  (i) *Reserved or presized arena storage, and scattered table growth* (`reserve_rehash`, `Space::push` 2.1%):
  presizing, 4x growth and fixed arrays were neutral, growth is below the benchmark noise of about ±5%, and whether 2%
  is worth having is open ("Arrays that never grow"; "Survey: where the growth comes from"). Trigger: a profile shows
  growth (`reserve_rehash`, `memcpy` from `Vec` growth) as a visible share of the build. Parked.
  (j) *The id arena's own parked items*: raw-`Ref` walks for `inst_rec`, `uses`, `conv_whnf`; a bitset for
  `hc::exceeds`; variable-length (12 B) nodes; in-process collection of the persistent space; a shared frozen
  persistent space; compiled code reading ids. The profile at 3407 shows no `resolve` ("Id arena Stage 3";
  `docs/superpowers/specs/2026-10-14-id-arena-spec.md`, "Parked", and the "Parked:" notes under "Stages"). Trigger:
  "if a profile shows `resolve`" (raw `Ref` walks); "if its walk shows" (the bitset). Parked.
  (k) *A quiet-machine rerun of the knee in ns per node against n*: best-of-4 under load had non-monotone steps larger
  than the knee ("ns per node against n after shared-only walk memos"). Trigger: the other sessions' jobs are gone.
  Parked.
- **One persisted-proof memo helper for `CLOSED` and the job's `tree_laws`** — why: both keep `(PExpr, PExpr)` made by `tatic::kernel::persist` and read back with `.get()`, by hand in two places; a helper beside `gen_memo` would hold that once. Code hygiene only, no speed in it; the other memos don't fit (`RewriteMemo`'s maps are carried across rule sets by trace, `OP_CACHE` is interning, the config-keyed statics are unrelated). Trigger: a third persisted-proof memo, or either one changing. Evidence: `CLOSED` in `tests/church_bv/rewrite.rs`, `job.lemmas.tree_laws` in `machine.rs` (its `Lemmas` field in `job.rs`), `gen_memo` in `encoding.rs` (2026-10-19 memo survey; symbols re-verified 2026-10-27). Status: parked.
- **Cache the built class table** — why: each process builds the table from the key file in about 0.6 s (1.5 s before 08adb24), once per long-lived worker; a cache file adds invalidation and format work for that. Trigger: the build exceeds a few percent of a worker's lifetime. Evidence: `docs/tier-cycle.md` ("A key refined by counterexamples"); `docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md`, decision 1 (2026-10-22). Status: parked.
- **Large `check_in` segments that commit only what they touch** — what: on Windows stacker's `CreateFiber(size)` commits the whole 64 MB `CHECK_SEGMENT`, about 150 MB of a sweep worker's 446-490 MB peak commit with two or three running at once; a fiber of our own (`CreateFiberEx`, small commit, 64 MB reserve) would drop it without the boundary crossings a smaller segment brings back. Why parked: commit charge only, no RAM (peak working set 221-304 MB), and two lanes peak at about 1.15 GB of commit. Trigger: commit charge becomes a limit (a commit-limit failure, or more lanes or threads per worker). Evidence: `docs/tier-cycle.md` ("What the rest of that peak is", 2026-10-23); `src/kernel.rs` `CHECK_SEGMENT`. Status: parked.
- **Winner-verdict cache across the sweep** — why: only about 3 of 65 proofs repeat with the same inputs. Trigger: none. Evidence: `docs/tier-cycle.md` ("Winner verdicts kept across the sweep (negative, reverted, 2026-10-13)"). Status: decided against.

## Sweep and miner throughput

- **In-memory lemma cache in the worker (the file goes)** — why: ceiling about 3% of busy CPU, about 0.4 s per sweep; recommended only "if any change is made". Trigger: measure what the reload costs first; none other stated. Evidence: `docs/tier-cycle.md` ("A persistent worker for the sweep's children"); `docs/superpowers/specs/2026-10-15-sweep-worker-design.md` ("Expected gain, and how it is measured"). Status: parked.
- **Sweep workers, lanes and thread pools** — what: more parallelism or reuse across the sweep's processes and threads
  than is built. Built: a sweep runs each stage's mines, then its loops, `SWEEP_LANES` (default 2) at a time, each mine
  with its scoring threads (397dcf2; salt 1 cold 386 to 199-236 s, `docs/tier-cycle.md`, "Lazy join steps, and sweeps
  in lanes"). Why parked, trigger and status per item:
  (a) *A worker pool inside a loop* (its mines and serves in parallel): within a loop each step reads files the earlier
  ones wrote ("A persistent worker for the sweep's children"; `docs/superpowers/specs/2026-10-15-sweep-worker-design.md`,
  "Parked"). Trigger: none stated. Parked.
  (b) *Reuse threads across tasks* (smallest step: a pool for the miner's prover threads): ceiling about 2-4%, below
  whole-sweep timing resolution; needs a scoped pool crate or unsafe code and a reset of task-local state ("Survey:
  reusing threads across tasks"). Trigger: none stated. Parked (not started).
  (c) *Persistent scoring workers carrying their memo*: no measurable gain, twice (before the join, job CPU 11.1 against
  10.4 s, branch `score-pool` on origin, 96b6e7e; with it, run `2026-10-17-join-pool`, join searches 3.4% fewer and mine time
  equal, `docs/runs/2026-10-17/patches/score_pool_join.patch`), since a chosen rule touches most join traces; and since
  2026-10-18 ruled out on correctness: a memo carried across a worker's candidates made the miner's choice depend on
  scheduling, so each candidate is scored from an empty memo ("The miner sees the join", the carried-memo bullet;
  "Fixed by a memo per candidate"). Trigger: an exact invalidation test that keeps more entries per round. Decided
  against.
  (d) *Two timed sweeps at a time* (background jobs plus `wait` in a multi-arm script, as
  `docs/runs/2026-10-17/scripts/gen_cost.sh` and `gen_twin.sh` could have): two sweeps of 2 lanes of 6 mining threads
  are 24 threads against the 12-thread cap, and lanes take the same parallelism inside a sweep (`driver::sweep`,
  `SWEEP_LANES`). Untimed gates do run arms concurrently, their verdict being counts (`JOBS` in
  `scripts/streams_ab.sh`). Decided against for timed runs.
- **Bound the class table's lookup memo** — what: `Classes::lookup`'s memo (values per term, and its answer) is a pure
  process-wide memo kept across a worker's tasks, like every `SharedMemo`, so it grows with every distinct term looked up
  (about 432 B of values each, plus subterms). Options: clear it per task, cap it, or key it per job. Why parked: the
  persistent worker keeps pure memos by design (`task.rs`), and growth measured so far is under the plan's 150 MB stop
  (largest `peakproc` +133 MB with the memo, +69 MB after the build's zip; short 3-loop gates). Trigger: a long sweep, or
  phase 2's step on every rewritten node, with peak commit past that stop or `Shared`/commit still climbing late in a
  run. Evidence: `tests/church_bv/classes.rs` (`Classes::lookup`), runs `2026-10-23-ct-memo-gate` and `-ct-zip-gate`
  (2026-10-23, final review I2); phase 2 built, on the old gate (run `2026-10-23-p2-gate-8`): memo peak 1690 terms in a
  worker process, largest `peakproc` 621 MB against 663 MB without phase 2, but its miner did almost nothing
  (`docs/tier-cycle.md`, "Phase 2 in the rewriter"); past the domain, on the streams gate (runs
  `2026-10-23-streams-aa-*`, salts 1-10): memo peak 8857-9712 terms, largest `peakproc` 1538 MB, all of it the stream
  sequence's generation (1537 MB alone, run `2026-10-23-stream-sequence-mem`; `docs/tier-cycle.md`, "The gate on the
  streams and its A/A baseline"), so the memo's share is still under the stop. Status: parked.
- **The class table's lookup beyond its domain, and under one lock** — what: `Classes::lookup` answers for nodes larger
  than the table's size or with an `lt` operand, by key values never refined to separate them; `step`'s verdict guards
  it, `canonical` (the twin filter) does not, so a false match can mark a law twin or trivial. And `lookup` computes a
  new term's values under the one process-wide lock, serializing the miner's threads; a known node that is not its own
  representative takes the lock twice (`rewrite_uncached`'s `lookup`, then `step`'s `rep`). Why parked: both are small today
  (the lock is inside 835 profile samples with reallocation). Trigger: a twin-filter gate showing wrong merges, or a
  profile of a streams sweep showing the lock. Evidence:
  `tests/church_bv/classes.rs` (`Classes::lookup`, `canonical`), final review M2, M3 (2026-10-23); phase 2 on the old
  gate (run `2026-10-23-p2-gate-8`): no `CLASS_UNUSABLE` with phase 2, job CPU 746 to 42 s, so the lock did not show there; past the
  table's domain: on the held-out files `held_out_replacements_prove` finds 0 false matches (the key's refuter refutes
  none of the 155 replacements `step` cannot prove, of 1743), so `canonical`'s risk is unobserved there; the lock's share
  is still uncounted (`docs/tier-cycle.md`, "The gate on the streams and its A/A baseline"). Status: parked.
- **Verdicts for replacements with a shift subterm** — what: past the table's domain `step` finds no proof for 4757-5272
  distinct replacements per streams sweep, every one with `shl1` or `shr1` in it, because `verdict` treats a shift
  subterm as a free atom (so it misses facts like `shr1(-1, 0)` being a constant); those nodes fall back to the rules,
  which is sound but leaves the miner work the table could do. Options: fold constant shift subterms before atomizing,
  or give `verdict` a per-position prover for shifts. Why parked: by decision; no unsoundness, and phase 2's gate is
  measured with the fallback in place. Trigger: a streams gate where the miner's rules are mostly over shift terms, or
  the next change to `verdict`. Evidence: runs `2026-10-23-streams-aa-*` (`CLASS_UNUSABLE` lines in each arm's logs),
  `held_out_replacements_prove` (155 of 1743 without a verdict, 0 refuted), 2026-10-23. Status: parked.
- **Skip replay arms that only confirm determinism** — a `*_full` file replay once one replay has matched its source run; saves about 30% of a replay probe. Why parked: by decision (2026-10-17). Trigger: a replay probe with more than about 3 arms. Evidence: `2026-10-17-gen-twin` (full replay reproduced all 90 rule files). Status: parked.
- **Serving reuses join results across batches** — why: nothing to reuse and little to save. Served batches are disjoint slices of the stream, so no pair repeats; serving's joins over salts 1-10 reached 1.36M terms in 1090 batches (about 4 s at 3 µs per term, against 21-25 s for one cmp3d mine). Trigger: a stream whose batches overlap. Evidence: the `m.tsv` files of run `2026-10-17-join-sticky` (arm b), `docs/tier-cycle.md` (same bullet). Status: decided against.
- **A lemma library that outlives the sweep (`LEMMA_KEEP`)** — why: speeds up nothing the benchmark measures (timings must stay cold), and `gate_cmp.py` removed the larger workflow cost; the survey recommends against. Trigger: many-salt studies of one build become routine. Evidence: `docs/tier-cycle.md` ("Survey: a lemma library kept across sweeps"). Status: decided against (the survey recommends not).
- **Smaller kernel-check levers: binder wrapping per law (about 1%); `InferCache` kept across `ck` calls (at most 4.3%, needs context-keyed entries in the trusted kernel); `CHECK_FAST` in cold loops and mines serving** — why: small, or changes what a sweep proves. Trigger: none stated ("last" for the cache). Evidence: `docs/tier-cycle.md` ("Survey: the kernel check's levers"). Status: parked (not built).
- **PGO on top of LTO** — why: gain over LTO (about -4%) is within noise; -6% against the default build and needs an instrumented build and training sweep on every code change. Trigger: none stated. Evidence: `docs/tier-cycle.md` ("Build flags: LTO, target-cpu=native, PGO"). Status: parked.
- **Bit-sliced screen vectors** (a term's screen values as n bit-planes of 204 bits instead of 204 `u128`s: 128 B at
  width 4 against 3264 B, one representation for every width; and/or/xor per plane, add and sub as a ripple carry over
  the planes; the tree-candidate index keyed by the planes). The memo is process-wide and never cleared. Why parked: it
  is about 11% of a worker's peak (56 of about 500 MB; the peak is set elsewhere in the first `rule_miner` task), though
  up to a third of its final commit (105 of 305 MB). A word chosen by width (`u8` up to width 8) was rejected as a
  per-width branch. Trigger: worker memory becomes a limit (more workers per lane, or the class table's per-worker
  memory), or `ValueMemo::fill`'s CPU share is worth a sliced evaluator (8.8% in the 2026-10-15 profile after the
  candidate index, 16.8-18.2% in two other profiles that day). At a mines' join
  budget of 100, `ValueMemo::fill` is 18.2% of the sweep's busy samples, about 17 points of it under the two stream
  builds and about 15 of those in `pool_conjectures`' exhaustive width-4 memos (run `2026-10-28-mjv-prof`). Those
  memos hold 4096 inputs, not the screen's 204, so this design would need 4096-input planes there (not measured).
  Evidence: `docs/tier-cycle.md`, "One screen memo and candidate index per process", its size in a sweep (2026-10-23),
  and "Grouping the streams' terms, and the 2-growth build inside the 4-growth one" (2026-10-28). Status: parked (by
  decision, 2026-10-23).
- **Contention in the shared screen memo at more than 6 miner threads** — why: wall did not move with CPU; the lock may be the cause, not measured. Trigger: none stated. Evidence: `docs/tier-cycle.md` ("One screen memo and candidate index per process"). Status: parked (untested).
- **Native Defender real-time-protection check when the service is running** — why: the `Component[2].fEnable` offset was not verified; the service is stopped on this machine, so the tool falls back to one PowerShell. Trigger: verify the offset against `Get-MpComputerStatus` on a machine with the service up (the user's call). Evidence: `docs/tier-cycle.md` ("Survey: workflow time outside the sweep"). Status: parked (untested).
- **Sweep-worker deferred bugs: unchecked Unix `dup`/`dup2` in `stdio`; case-sensitive `process_start` prefix match; a panic during flush leaves the std handle on a dropped `File`** — why: deferred as minor. Trigger: none stated. Evidence: `docs/tier-cycle.md` ("A persistent worker for the sweep's children"). Status: parked.
- **A shorter quiet wait before each `runs time` round (`--quiet-secs` 10 against 60)** — why: the waits were 37 of `lazy-quiet`'s 69 minutes, but an A/A at 10 s under a busier machine gave 1 clean round of 9 (run `2026-10-19-lazy-aa-q10`), which cannot be told apart from the load having changed since. Trigger: A/B wall time matters again; the test is the two waits alternating in one session (an A/A at each), comparing clean rounds per hour and the noise around each run order's mean. Evidence: `docs/tier-cycle.md`, "A shorter quiet wait before each round", verified 2026-10-19. Status: parked.
- **Build the stream sequence lazily, only as far as it is read** — what: a sweep
  reads only positions under about 1200 of the loops' 58125-law sequence (phases 1-3's first 300 laws, stride 4) and,
  since 66a9810, about the first 2600 of the extras' 230801-law 4-growth one (salt 1, until 6 × 319 laws pass the
  filter); the 4-growth build took 28.4 s on 4 threads (4 × 28.4 s is about 12% of salt 1's 959 s of job CPU, an
  estimate) and a sweep peaks at 5-6 GB (runs `2026-10-28-land-n319`, `-mjv-j250`, `-mjv-j100`). At a mines' join
  budget of 100 it was profiled: 34.0% of the sweep's busy samples, and the 2-growth build 12.4% more (run
  `2026-10-28-mjv-prof`). Before 66a9810 the extras read phase 0's first 1650 of the 2-growth one. `stream_laws`
  filters (class-table normal forms, width-8 values) after `shuffled(laws, salt)`, so lazy streams stopped at the read
  prefix give identical laws (cleanup plan CU17); a memo of normal forms in the same filter (CU16) landed 2026-10-29
  as F1 (`docs/tier-cycle.md`, "F1 landed"). Why not (2026-10-27): growing and grouping a stream's terms
  (`pool_conjectures`) is paid in full either way, and since the per-tuple `verdict` loop went (CU15) the filter is
  2.6% of a base sweep's samples against 5.8% for grouping; the sequence as a whole fell from 109.5 to 23.3 s and is
  10.6%. The lazy build saved at most that 2.6% then, and it changes `stream_sequence`'s interface (a length per
  caller, or a locked lazy type). The sequence's wall share went instead to building the 56 independent streams in
  parallel (cleanup plan CU18: 16.1 to 5.4 s on 4 threads, `docs/tier-cycle.md`, "The streams in parallel"). The
  4-growth build is the same shape, and laziness again saves at most its filter: 33% of that build at budget 100, about
  11% of the sweep, while
  grouping is 52% of it (about 18% of the sweep: the exhaustive width-4 value vectors and, until `cd7dacb`, each
  term's 4097-byte group key) and growth and sorting the rest, all paid in full (`docs/tier-cycle.md`, "A join budget
  for the mines alone"). Trigger: the filter grows again (a costlier open or refutation check), or the 4-growth
  build's cost matters: met 2026-10-28 if the mines' join budget lands at 100. Evidence: runs
  `2026-10-26-cu14-base-prof` and `2026-10-27-cu17-base-prof` (`PROF_PARENTS` split of `stream_laws`, 2026-10-27),
  `2026-10-28-mjv-prof` (`PROF_THREAD` by the builds' thread ids); `docs/tier-cycle.md`, "One exhaustive check for
  both". A probe split the build and found the loops' 2-growth build inside the extras' 4-growth one
  (`docs/tier-cycle.md`, "Grouping the streams' terms, and the 2-growth build inside the 4-growth one", run
  `2026-10-28-stream-probe`; deriving the first from the second is the entry "Derive the 2-growth sequence from the
  4-growth build"), and value-class ids for grouping were chosen (2026-10-28). Since F1 the filter is 35.6% of the pin
  test's busy samples against 43.1 before (runs `2026-10-29-f1-prof`, `-f3-prof`), so a lazy build saves less.
  Status: decided against (2026-10-27), held for the join budget's landing with cheaper grouping the larger lever
  (2026-10-28).
- **Derive the 2-growth sequence from the 4-growth build** — what: keep each stream's 4-growth list with each law's
  depth and merge the lists restricted to depth 2, instead of building the 2-growth sequence separately; filtering the
  merged 4-growth sequence is not exact. Design options (the user's call): (a) one memo per salt holding the
  depth-tagged lists at the deepest depth asked so far, `stream_sequence(salt, levels)` unchanged as a view, callers
  asking for the deep sequence first (`scope_extras`, `regenerate_held`, the pin test); (b) the same lists always built
  at the deepest band's depth, so the memo is keyed by the salt alone and no order matters, while processes that need
  only 2 growths (and both salts under `GEN_DRAW`) pay a 4-growth build (2.3-2.7 times the 2-growth one); (c) a call
  that takes every depth at once (`stream_sequences(salt, &[2, 4])`), hoisted into `sweep` and `from_env`; (d) leave
  the two builds. Related, one line: `scope_extras` builds the 4-growth sequence even with `EXTRAS_N=0`. Why held: a
  change to `stream_sequence`'s memo and `stream_laws`' return type, and its net saving is not counted (at most the
  2-growth build, 6.5 of 22.8 s under samply, about 69% of it once the cold-memo fill that moves into the 4-growth
  build is taken off). Trigger: the user picks a design; the first step is a per-stream test that the restricted
  4-growth list equals the 2-growth list at several salts, then a count of the pin test before and after. Evidence:
  `docs/tier-cycle.md`, "Deriving the 2-growth sequence from the 4-growth build" and "Grouping the streams' terms, and
  the 2-growth build inside the 4-growth one" (2026-10-28). Status: held for the user's call (2026-10-28).
- **Cheaper first asks in the stream builds** — what: the once-per-process work `Classes::normalize` does for a term
  it has not seen (6.78 s, 14.8% of a quiet one-thread 4-growth build before `cd7dacb`; 1.00 s of it was
  `bitwise_holds`' exhaustive inputs, built once per process since F3, `docs/tier-cycle.md`, "F3 landed"). Pieces,
  each exact: write the `CLASS_UNUSABLE` lines in one batch rather than one `println` each (1.04 s, about 100 µs a
  line); take the `CARRY_CAP` read (`Setup::var`: a string-keyed
  map and a lock) off the path of each of the 4.49 M steps that have a representative (not measured); carry verdicts
  and lookups across processes (5.73 s, needs a stored format and its invalidation). Why held: found by a probe on
  one thread, not yet weighed against the sweep (the two builds were 46% of the busy samples at a join budget of 100,
  run `2026-10-28-mjv-prof`) or counted. Trigger: the user's call, or a count of the pin test showing normalize's
  misses still above about 10% of a build after `cd7dacb`. Evidence: `docs/tier-cycle.md`, "Why normalize is slow on
  a cold stream" (runs `2026-10-28-normalize-cold*`, 2026-10-28). Status: held for the user's call (2026-10-28).
- **Options held behind the filter, `show` and purge survey** — what: P1, mimalloc's purge off in the harness
  (`mi_option_set(15, -1)`, spiked and reverted: `docs/runs/2026-10-29/patches/purge_spike_on_ab9eeba.patch`);
  P2, `arena_reserve` at 256 MiB; P3, a mimalloc patch that keeps the purge expiry current. Decided against
  2026-10-29: S4, presizing `show`'s `String` (`Term::show` is 0.03% after S2). Landed, no longer held: S3, the sorts
  (2026-10-29; `docs/tier-cycle.md`, "S3 landed": 0.63% of busy samples remain, the seeds sort's, which stays since its
  order picks the terms the growth samples); F2, a plan-free `normalize` for the open-law filter (2026-10-30; "F2
  landed": -2.4% in a count). Also landed: `Term`'s `Ord` as the text order, `show_cmp` deleted and the string-keyed sorts converted (2026-10-30; "Ord landed": +0.09% in a count, no speedup claimed). P1 landed 2026-10-30 in the harness, on the user's call ("P1 timed": the env var read -7.3% job CPU at one
  pinned thread, 8 of 8 rounds, peak memory unchanged; "P1 timed again": on the current base the env var and the landed build both read
  about zero, 3 clean rounds, peak memory unchanged). Why held (P2, P3): they matter only if purge-off leaves a gap, and there is no
  measured saving left to complete. Trigger: the F2-exe rerun of the three arms (falsifier in "P1 timed again") brings the -7.3% back and the
  landed build falls short of it, or peak memory grows; then P2 or P3. Evidence: `docs/tier-cycle.md`, "Survey: the
  open-law filter, `Term::show` and mimalloc's purge" (profile `2026-10-29-zerofill3-prof`, 2026-10-29), its "P1 spike"
  paragraph, "P1 timed" (run `2026-10-30-purge-time3`) and "P1 timed again" (run `2026-10-30-p1-time2`). Status: P1 landed (equivalent to the env var, saving not reproduced on the current base); P2 and P3 held. Also parked: a
  timed four-thread P1 A/B (`purge_time_land.sh <old> <new> 8 4 3300`); 14 launches on 2026-10-30 (`2026-10-30-p1-time4t{,2..14}`) were all
  refused by the quiet-machine gate (other sessions' `manifold` and `rustc` jobs, games), so the only four-thread evidence is the untimed
  spike (-10.6%). Trigger: a quiet machine (`run.ps1 -Timed` accepted).
- **A prefilter before the full value vectors** — what: in `pool_conjectures`, group the terms first by their values
  on 16 fixed inputs and fill full width-4 vectors only for terms that share a bucket; exact, since equal vectors agree
  on any subset. Why parked: 52% of a stream's terms are in true groups, so it can skip at most about half the fills;
  it halved fill, key and insert time in aggregate but was slower on 11 of the 55 streams whose single stage takes
  0.05 s or more (4 growths), and it adds a second memo and a tunable; value-class ids (one id per distinct vector, no
  copied keys) were chosen first. Trigger: after the ids land, filling vectors is still about a third of a stream
  build by a fresh count. Evidence: `docs/tier-cycle.md`, "Grouping the streams' terms, and the 2-growth build inside
  the 4-growth one" (run `2026-10-28-stream-probe`, 2026-10-28); after the ids (`cd7dacb`), filling under
  `pool_conjectures` is 28.6% of the busy samples of building both sequences (`zip_op`; run `2026-10-28-class-ids-prof`);
  with `zip_word` on native bytes (landed 2026-10-29, `a63ff57`, `7637e88`) it is 7.5% (run `2026-10-29-typedrows-prof`),
  and 8.8% (`fill_op`) once the fill stopped zeroing first (`c8c2e68`; run `2026-10-29-zerofill3-prof`).
  Status: parked, trigger not met (2026-10-29).
- **Operators as an `enum Op`, with their bit-level and kernel forms in the rows** — what: replace the `usize`
  operator ids (`rewrite.rs`'s `ADD` to `SHR1`) with an `enum Op` whose `info()` gives the typed row, so the wildcard
  dispatchers become exhaustive matches and a new operator is a compile error wherever it needs handling; and derive
  from the rows what is now restated beside them. Bit-level forms: `OpInfo::truth`, `Term::bit`, `machine::term_gb`,
  `machine::BIT_OPS` (`pos_bit`), `Machine::step`'s `and`, `or` and `xor` arms, and the `good2(.., &OP_INFO[k].truth)`
  calls (`witnessed`'s three arms; and/or/xor triples in `encoding.rs`'s `good_ripple`, `good_lt` and `GoodOps::new`;
  `good_or_bv`'s lone `or`). Kernel forms, the Church-encoded operators and their witness lemmas: `ops_for` (an
  `[Expr; 8]` in `Node::Op` order, held as `Compiler::ops`) and `witnessed`'s `good_add`, `good_sub`, `good_shl1` and
  `good_shr1` arms. Also in `Node::Op` order by hand: `zip_op`'s eight `zip_word::<W, k>` entries (its length is tied to
  `OP_INFO.len()`, the order is not) and the test `operators_match_a_bit_at_a_time`'s `by_bits` (by name, ending in
  `_ => panic!`). Why parked: by decision 2026-10-29, typed rows alone landed (`7637e88`) and this was surveyed as a
  separate change. The
  dispatchers today: `witnessed` (`rewrite.rs`) sends every operator but `add`, `sub`, `shl1` and `shr1` to an
  `and`/`or`/`xor` match ending in `_ => xor`, so an `lt` there would be witnessed as `xor`; not reached as far as
  checked, since `lt` terms occur only at roots (`miner.rs`, the pool's doc comment) and a law's arguments are subterms
  below its match. `Machine::step` (`machine.rs`) treats every operator but 1, 2, 3 and 6 as an adder, a subtractor
  when `o >= 4` (`lt` is `sub`'s borrow; `parse` rejects `shr1`); `Machine::last` and `shift_k` use bare 5, 6 and 7;
  `classes::OPS: [usize; 8]` is not tied to `OP_INFO.len()`. A one-byte `Op` would make `Node` 24 bytes instead of 32
  (its size is asserted in `rewrite.rs`) and each interned node 8 bytes smaller, which moves the addresses terms hash
  by (`op_hash`) and the memory per term, so it needs its own count. Trigger: the user's
  call, or a ninth operator. Evidence: the call sites above (2026-10-29). Status: parked (by decision, 2026-10-29).
- **One value memo shared by the streams** — what: one process-wide exhaustive width-4 memo for every stream's
  `pool_conjectures` instead of one per stream. Why: only 12.6% of the 8.11 M fills at 4 growths repeat another
  stream's (19.8% at 2), and the 7.09 M distinct terms would take 29 GB at 4096 bytes each. Trigger: none stated.
  Evidence: `docs/tier-cycle.md`, "Grouping the streams' terms, and the 2-growth build inside the 4-growth one" (run
  `2026-10-28-stream-probe`, 2026-10-28). Status: decided against (2026-10-28).
- **Binary formats for the sweep's text files: task results (C7's `key<TAB>value` channel), rule libraries (`rules.txt`, `laws_extra_*.txt`), law files (`laws_text`), the `m.tsv` tables** — why: each is KB-sized and written once per task, the payloads are terms already printed as text, the text is the evidence a reader greps and diffs, and a binary form needs a reader for every consumer (scripts included). The lemma cache, the one large and hot store, is already binary (`TLC1`, `tatic::kernel::bin`). Trigger: any of these files reaching MB or showing in a sweep profile (parse or format time). Evidence: the writers in `tests/church_bv/driver.rs` (`laws_extra_*`, `m.tsv`), `laws_text` in `search.rs`, the lemma cache's `TLC1` format in `lemma_cache.rs` (2026-10-21; the prefs and joinability-unit files no longer exist, checked 2026-10-27). Status: parked (by decision, C7 ruling 2026-10-21).

## Code hygiene

- **Typed lemma keys (`CLOSED`, `guarded`'s tree key, `Machine::key`, `shared_lemma`)** — why: no speed value (formatting is 0.0% of the profile); a cleanliness item. Trigger: none stated. Evidence: `docs/tier-cycle.md` ("Structural term equality (kept, 2026-10-12)"); `docs/superpowers/plans/2026-10-12-proof-plans.md` ("Tasks"). Status: parked.
- **Unification passes #4-#7 (atomize only vars/add/sub/lt; delete hand-written `x+0` arms; `pos_law` for `bitwise_law_k`; ADD assoc/comm into `rules()`)** — why: no law found that #4 proves; #5-#7 change proof sizes, timing or ordering. Trigger: #4: shifts-over-adds become a goal; others none stated. Evidence: `docs/superpowers/specs/2026-10-05-loop-summary.md` ("Unification passes (2026-10-09/10): done and parked"). Status: parked.
- **Kernel work instrumentation (`record-defeq`: per-traversal visit counts, beta steps, nodes built, the defeq log, `law_work_report`, `walk_counts_on_hard_queries`) and the `kernel_lazy` evaluator** — why: deleted from the trusted kernel (38 probe sites, 26 hand-numbered slots); their findings are in `docs/tier-cycle.md`'s tables. The total is now `kernel::work()` (0cf04c6, always on, one tick per worker call, no feature flag), so a revert is no longer the way to get a work count. Trigger: a question that needs the per-traversal split (not the total), or a second evaluator to test `def_eq` against; restore with `git revert 306a968` (expect merges against later kernel changes, C6's `Checker` first). Evidence: commit 306a968, 2026-10-21. Status: parked (removed by decision, C11 ruling 2026-10-21).
- **Ignored probes nothing cited** — (a) nine (`scaling_probe`, `skeleton_probe` with `add_mode`'s skeleton modes, `add_comm_scaling`, the 64-bit conv add, `profile_add_zero_n256`, `raw_table_probe`, `machine_lemma_probe`, `lemma_overhead_probe`, `three_var_probe`), commit 7865865, 2026-10-21 (C13); (b) the 2026-09-30 bitvector spec's probes (`shared_carry_scaling`, `proof_size_scaling`, `add_zero_lemma_scaling`, `add_comm_rejection_probe`, `add_shared_zero_scaling`, `whole_check_time`, `table_lookup_cost_by_size`), `tree_proof_cost_by_carries` and `tests/proof_scope.rs` (scoped against unscoped universal proofs, DAG against tree size), cleanup CU7, 2026-10-27. Why: no live doc, script or entry named them; only done specs, read as history. Trigger: one of their questions coming back; restore with `git revert` of the named commit. Status: parked (removed by decision).
- **Counters as return values (machine fallbacks, cycle cuts, join cost returned by rewriting rather than accumulated in the job)** — why: by decision 2026-10-21; the rewrite-context plan (`docs/superpowers/plans/2026-10-21-rewrite-context.md`, D1) moves them into `Job`, and cleanup C2 (2026-10-22) turns the callers' before/after delta reads into one `Job::measured(budget, f)` / `Job::spent(f)` call returning a `Spent`. Trigger: the delta reads grow again or cause a bug. Evidence: after C2 (2026-10-22, `grep -nE "= *job\.(rw\.(budget|fallbacks|cycle_cuts)|join_cost)|\(job\.rw\." tests/church_bv/*.rs`) no caller snapshots a counter. What is left: `Job::spent` itself and the rewriter's own memo and replay bookkeeping (`rewrite_memo`, `check_replay`, `rewrite_law`'s per-side budget in rewrite.rs). Status: parked.
- **Class-table loose ends (final review M6, M7, 2026-10-23)** — the table pin and `class_hash` use std's `DefaultHasher`, whose algorithm a toolchain update may change (the pin would fail with the table unchanged); `mi_collect` and `mi_option_get` (with the option's id as the literal `6`) are declared by hand, since `mimalloc` keeps `libmimalloc_sys` private (`extern crate libmimalloc_sys as ffi`), so a typed binding needs `libmimalloc-sys` as a direct dependency with its `extended` feature. Why: latent, no wrong answer today. Trigger: a toolchain bump failing the pin, a `mimalloc` upgrade, or a third mimalloc function (P1 in `docs/tier-cycle.md`, "Survey: the open-law filter, `Term::show` and mimalloc's purge", if it lands; its spike ran 2026-10-29). Evidence: `tests/church_bv/classes.rs` (`class_hash`, `Classes::get`, `the_full_table_is_pinned`), `tests/church_bv/machine.rs` (`large_pages_option`), 2026-10-29. Status: parked.
- **A search or space-growth counter beside `kernel::work()` (f2)** — what: a second deterministic counter for the cost `work()` leaves out, so a model reward or a library comparison tracks build time where `work()` ranks it wrong. Why parked: `work()` already tracks per-law time at rho 0.93-0.97, and a `rule_step` search tick (h2) tracked 0.26-0.33 and was reverted; search (`rewrite_plan` with the class table build, the join) is 3-4% of a held-band build. The only gap found is the mined library, which cuts time per work unit by 10-20% (interleaved ABAB on band 17: 545 against 667 us per 1000 work units; sequential runs overstated it at 30-35%) while `work()` rises 4%; a space counter (nodes pushed, reallocations, copy volume) does not explain it (pushed tracks `work()` at 0.42-0.47 per unit; reallocations are rare; copy volume is equal between arms). Trigger: a consumer that must rank library or plan choices by time and sees `work()` mis-rank them by more than that 10-20%; then profile cache behaviour, not counts. Evidence: `docs/tier-cycle.md`, "Work in place of M, replayed" and the three paragraphs after it (runs `2026-10-30-work-vs-m-spike5`, `-build-prof-h17b`, `-space-growth-spike`, `-space-growth-abab`), 2026-10-30. Status: decided against a counter for now (parked: the remaining gap is unexplained).
- **The undeletable run folder `%LOCALAPPDATA%\claude-runs\tatic\2026-10-30-build-prof-h17`** — what: an empty folder from a mis-launched profile (the run was relaunched as `build-prof-h17b`; its `docs/runs.md` row is removed). Why parked: `rm -rf` fails ("Device or resource busy"); no live wrapper of this session holds it, so a stale handle is the guess (unverified). Trigger: a reboot, or the folder showing up in a retention sweep. Evidence: `docs/runs.md` has no row for it, 2026-10-31. Status: parked (delete it after a reboot).
- **Stale comments and doc lines found by the tour survey (2026-10-31)** — what: (a) `kernel_verify`'s doc in `src/jit.rs` says an `If` between two closures is out of scope for `prove_closure_expr`, which now accepts it; (b) `prove_eq`'s doc comment lists the class table's normal forms as a step the body no longer has, and `docs/tier-cycle.md` has a note describing the deleted step; (c) `docs/tier-cycle.md`'s proof-plan paragraph lists `LawKind::Chain`, removed from the enum; (d) `Machine::carries`' doc says only add or sub nodes carry, but `shl1` and `lt` do too; (e) a comment in `src/kernel/postulates.rs` says `cong_n` is not yet used by the straight-line proof, and `src/proof/hardening.rs` calls it; (f) `docs/learned-vs-fixed.md` names `set_extra_rules` and `rules()`, which occur in no `.rs` file (live: `with_rules` in `tests/church_bv/job.rs`, `build_fixed_rules` in `tests/church_bv/rewrite.rs`); (g) a "cumulative greedy" doc comment in `tests/church_bv/miner.rs` sits on `Scorer`'s scoring method, not on the rounds it describes; (h) `docs/superpowers/plans/2026-10-27-test-terms-as-source-inventory.md` has no `status:` line. Why parked: comments and docs only, no behavior. Trigger: the next edit of any of those places (fix it then). Evidence: `docs/TOUR.md` survey, claims read in code by agents on 2026-10-31, not re-read by hand. Status: parked.

- **Learned target-cost model** — what: a model of how fast the target code runs, trained from `wasmtime` timings of lowering candidates, ranking lowerings beside size- and M-scored mining; untrusted, so a wrong model costs speed only. Why parked: needs a workload with arithmetic depth to show anything (the goal 1 blocker), and the belief layer (a3) comes first as its substrate; its first milestone stopped at its gate (see "Belief layer stage 2"), so no layer exists yet. Trigger: a usable belief layer exists and a workload with arithmetic depth does. Evidence: `docs/decisions/2026-10-31-learned-target-model.md`; the "Compile hot transformations" entry. Status: parked.
- **Execution-learned model for an unformalized target** — what: a model learned from executing instructions on a target with no formalization (native ISA), giving sample-tier equivalence only. Why parked: the installation gate accepts only kernel proofs over every input, so sample-only installs need a policy decision first. Trigger: a decision to allow a sample tier, or a target whose formalization is out of reach. Evidence: `docs/decisions/2026-10-31-learned-target-model.md`; the "Native ISA semantics below wasm" entry. Status: parked.
- **Belief layer stage 2: score unprovability (or the cheap path's misses)** — what: the counts and logistic arms, the grouped-fold comparison and the paired bootstrap of `docs/superpowers/specs/2026-10-31-belief-layer-design.md`, rerun with "unproved" as the negative class (A_unp: 2693 of 63384 screen-pass claims). Why parked: the spec's headline score A_ref had 0 hard negatives, so stage 2 never started; moving the headline to A_unp changes the spec's question (the comparator is no longer the screen, which cannot see unprovability) and needs a decision. Alternative to weigh beside it: keep refutation as the score but count width-4 failure as evidence rather than as part of the subset, so the 370 claims that pass the screen and fail only width 4 become the negatives (above the 100 gate; the screen-only comparator then has something to miss). Update 2026-11-01: all 2693 unproved claims are provable at width 4 by `prove_rule` (spike, same section), so A_unp would predict which claims the cheap `verdict` path misses (2652 contain `shr1`), a cost question rather than a truth one. Trigger: a decision on that question, or a claim source whose screen-pass claims are refuted (a proposer's, i2). Evidence: `docs/tier-cycle.md`, "The belief layer's calibration milestone stops at its first gate" (runs `2026-11-01-belief-dump-all-2`, `-shr1-spike-3`, `-shr1-spike-4`); code kept in `tests/church_bv/belief.rs` (`belief_counts`, `cells_at`, `logistic_fit`, `paired_bootstrap`). Decided 2026-11-01 (f1): not run. Predicting `verdict`'s miss is predicting a deterministic function that costs milliseconds, with no consumer, and a high AUC is foreseeable from the 2652-of-14904 `shr1` split; the written design is `docs/superpowers/specs/2026-11-01-belief-cost-design.md` (draft, unapproved) for a claim source whose label costs more than the model. Status: decided against, trigger as above.
- **LLVM InstCombine tests as a corpus for the table and mined rules** — what: the integer-only functions of `llvm/test/Transforms/InstCombine` (about 1,700 entries of typed `.ll`) translated into the loop's term language, as a second external corpus beside Souper's. Why parked: by decision (2026-11-01): far larger translation work (an LLVM IR parser, filtering memory, casts, vectors, floats, `mul`/`div`) and a less fixed selection than Souper's `test/Infer`; the Souper corpus is run first. Trigger: the Souper run finds the table or mined rules matter on external code and a wider sample is needed. Evidence: directory listing read 2026-11-01 (file contents not opened). Status: parked.
