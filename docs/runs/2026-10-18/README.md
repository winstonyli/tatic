# Runs of 2026-10-18

Rows behind `docs/tier-cycle.md`, "Lazy join steps, and sweeps in lanes". Each run is recorded in `docs/runs.md` with its
raw folder under `%LOCALAPPDATA%\claude-runs\tatic\<run id>`. Builds were `cargo test --profile sweep --test church_bv
--no-run`, copied to `$TEMP/bv_<name>.exe`: `bv_jprobe` (6e621ca + `patches/join_count.patch`), `bv_lanes` (397dcf2's
tree: lanes, eager join), `bv_lazy` (7ee55b3's tree before its last refactor) and `bv_lazy2` (7ee55b3). The rows of the
morning's generator rounds are in `docs/runs/2026-10-17/README.md`.

- `patches/join_count.patch`: the probe's counters (neighbours built, new and already reached; spine rebuilds; the
  operator-invariant cut) and their `RULEMINER join` print line. It applies to 6e621ca.
- `scripts/lanes_check.sh <exe> <salt>`: one sweep per lane count in `LANES` (default `1 2`) per arm in `ARMS` (default
  `all cold`: the default SWEEP with `ABLATE=gen`, and `SWEEP=cold` with extras), wall seconds, and whether the arm's
  first two sweeps agree (`../2026-10-17/scripts/same_arms.sh`). Runs with a single sweep per arm print a verdict line
  against a sweep they did not make; their rows compare by hand.
- `scripts/history_check.sh <exe> <salt>`: `SWEEP=cold:cmp3d` at 1 lane, 3 lanes and 1 lane with `LEMMA_RECHECK=1`, and
  which loops' rules agree with the 3-lane run.
- `patches/join_check2.patch` (on e654360, exe `bv_jcheck`): `JOIN_CHECK`, rerunning the join search on every memo hit
  and counting flips and differing traces. `scripts/join_check.sh <exe> <salt>`: one `SWEEP=cold:cmp3d` with it on.
- `patches/join_exact.patch` (on e654360, exe `bv_jexact`): `JOIN_EXACT` (a met join keeps every examined term in its
  trace) and `LOOP_THREADS` (the scoring workers of mines and loops, default 6). `scripts/join_exact.sh <exe> <salt>`:
  `SWEEP=cold:cmp3d` as built and exact, at 6 and 1 threads, and which arms' rule files agree.
- `patches/lazy_prof.patch` (on e654360, debug info): `driver::sweep_prof`, salt 1's cold cmp3d loops on one lane with the
  environment set in the test. `scripts/lazy_prof.sh <exe>`: the samply profile. `scripts/prof_named.py <dir> <exe>
  [leaf...]`: self and inclusive shares by function, naming the exe's frames with llvm-symbolizer (samply could not: the
  PDB must sit beside the exe under the name the exe records), and the callers of the named leaves.
- `patches/match_count.patch` (on a49d1af, exe `bv_mprobe`): `JoinCost.probe`, ten counters of the join's matching, step
  terms and `Term::op` (fields in the patch's header), printed per mine. `scripts/match_count.sh <exe> <salt>`: one
  `SWEEP=cold:cmp3d` and the counters' sum.
- `patches/size_bound.patch` (on e450d24, exe `bv_sbound`): counters of what a size bound before matching would skip
  (fields in the patch's header), run with `match_count.sh`.
- `patches/join_paths.patch` (on a615974, exe `bv_jpaths`): `JOIN_PATHS`, each met join search's path with its size
  changes per side. `scripts/join_paths.sh <exe> <salt>`: one `SWEEP=cold:cmp3d` and the uphill-step summary.
- `patches/cost_join.patch` (on a615974, includes `join_paths.patch`; exe `bv_cjoin`): `JOIN_SHADOW`, a join bounded by
  size-increasing steps run beside the real one on a sample of pairs (fields in the patch's header).
  `scripts/cost_join.sh <exe> <salt>`: one sweep per budget in `BUDGETS`, the outcomes against the real join's and the
  terms reached.
- `patches/cost_join_ac.patch` (on a615974, includes `cost_join.patch`; exe `bv_cjac`): `JOIN_AC=1`, the shadow with flat AC steps
  skipped and terms in a canonical AC form; run with `cost_join.sh`. `patches/cost_search.patch` (on a615974, includes
  `cost_join_ac.patch`; exe `bv_sbnd`): `JOIN_COST_BOUND=<budget>`, the bounded join replacing the real one in the
  serving worker. `scripts/serve_bound_ab.sh <exe> <salt>...`: per salt, `SWEEP=cold:cmp3d` as built and with
  `JOIN_COST_BOUND=4`, a 12 GB watchdog, and each loop's M and rules compared.
- `scripts/exact_salts.sh <exe> <salt>...`: per salt, `SWEEP=cold:cmp3d` as built and with `JOIN_EXACT=1` (exe `bv_jexact2`,
  10a8a50 + `patches/join_exact.patch`), wall seconds, each loop's M and rules compared, and totals.
- `patches/serve_shadow.patch` (on 10a8a50, `cost_join.patch` plus `JOIN_SHADOW_SERVE=1`; exe `bv_cserve`): the shadow on
  every join search of the serving worker, none of the miner's, with both terms. `scripts/serve_shadow.sh <exe>
  <salt>...`: one `SWEEP=cold:cmp3d` per salt and the outcomes against the real join's.
- `patches/memo_per_cand.patch` (on ae96a7e, includes `join_exact.patch`; exe `bv_snap`): `MEMO_PER_CAND=1`, each scoring
  worker starts every candidate from an empty memo. `scripts/snap_salts.sh <exe> <salt>...`: per salt the arms in `ARMS`
  (default `base6 snap6 snap1`), M per loop, rules of snap6 against base6 and of snap1 against snap6, and totals.
- `scripts/threads_check.sh <exe> <salt>`: the built check: `SWEEP=cold:cmp3d` at `LOOP_THREADS` 6 and 1 and whether every
  loop's rules agree.
- `scripts/interner_ab.sh <exe A> <exe B> <salt>`: `SWEEP=cold:cmp3d` at 1 lane in the order A B B A, wall seconds, and
  which sweeps' files agree with A's first. A was `bv_lazy2`, B `bv_lockfree` (a49d1af with the lock-free interner).
- `scripts/arms_ab.sh <salt> <exe>...`: the same for any number of exes, in order and then reversed, with a memory
  watchdog. `bv_base` was 31e0903, `bv_sb` 8de04c1 (the size bound), `bv_both` 2de4854 (and the interner's tags); the
  rows file adds each sweep's `RULEMINER join` lines.
- `scripts/quiet_ab.sh <salt> <rounds> <exe>...`: the same arms through `runs time` (alternated, job CPU and wall, a
  round kept only while others' load is low), then which runs' files agree with the first's.
- `scripts/salts_ab.sh <exe A> <exe B> <salts...>`: `SWEEP=cold:cmp3d` per salt with A and B (A first on odd salts),
  each a `runs run`; per loop the M of each and whether their rules agree, then per arm the totals of M, wall and job
  CPU; since 2026-10-23 also the mines' rounds and lookahead decisions, per loop and per arm. A was `bv_old` (dc2102c, before the memo per candidate), B `bv_both`.
- `scripts/prof_timeline.py <dir>`: a samply profile's wall by how many threads are busy at once, split into the miner's
  main thread and its scoring pool, and cores busy per second. `prof_named.py` takes `PROF_THREAD=<name>` to keep one
  thread name's samples (table in `named_<name>.txt`), and `PROF_PARENTS=<frame>,...` to list what each named frame calls
directly (to tell numbered closures apart). `bv_lprof3` is 3a851d6 with `patches/lazy_prof.patch`, debug info.
`rows/2026-10-18-aff-prof-timeline.txt` and `-aff-prof-main.txt` are its timeline and main-thread tables.
- `rows/<run id>.txt`: each run's `out.log`; `rows/2026-10-18-lazy-prof.txt` is `prof_named.py`'s table; `rows/2026-10-18-pcand-timeline.txt` is `prof_timeline.py`'s on
`-pcand-prof`, and `rows/2026-10-18-pcand-prof-main.txt` the main thread's `prof_named.py` table. `rows/lanes-check_cold_l{1,2}_cmp3d_2_mine_0.log`: the first mine of the
  loop that differed between `-lanes-check`'s sweeps.

| Run | Build | Script | Result |
|---|---|---|---|
| `2026-10-18-join-count` | `bv_jprobe` | by hand: `SWEEP=cold:cmp3d`, salt 6 | 58% of neighbours already reached; invariant cut 0 |
| `2026-10-18-lanes-check` | `bv_lanes` | `lanes_check.sh` (its first version), salt 1 | cold 386 s at 1 lane, 236 s at 2, one loop differs |
| `2026-10-18-cold-repeat` | `bv_lanes` | `ARMS=cold LANES=1` | 366 s, as the 1-lane sweep |
| `2026-10-18-loop-history` | `bv_lanes` | `history_check.sh` | no history through worker or lemma file |
| `2026-10-18-cold-l2-repeat` | `bv_lanes` | `ARMS=cold LANES="2 2"` | 223 and 199 s, both as the 1-lane sweep |
| `2026-10-18-lazy-join` | `bv_lazy` | `LANES=1` | cold 154 s, every file as the eager join's |
| `2026-10-18-eager-join-ab` | `bv_lanes` | `ARMS=cold LANES=1` | cold 331 s, the A/B for `-lazy-join` |
| `2026-10-18-lazy-lanes2` | `bv_lazy2` | `LANES=2` | cold 99 s, every file as the eager join's |
| `2026-10-18-join-check` | `bv_jcheck` | `join_check.sh`, salt 1 | kept join entries flip (up to 65 per lane worker) and differ in trace (up to 790) |
| `2026-10-18-join-exact` | `bv_jexact` | `join_exact.sh`, salt 1 | threads change loop 15-2 as built, nothing with `JOIN_EXACT`; exact 108 s against 66 s |
| `2026-10-18-lazy-prof` | `bv_lprof` | `lazy_prof.sh` | join 82.7%; `Term::op` 28% (mutex 8.5%), `match_pat` 19.4%, `subst_sig` 12.2% |
| `2026-10-18-match-count` | `bv_mprobe` | `match_count.sh`, salt 1 | matcher fails 60%, 59% of matches over the cap; 37% of step terms expanded; `Term::op` 26.2% table hits, 0.35% new |
| `2026-10-18-pcand-prof` | `bv_lprof2` | `lazy_prof.sh` | join 85.3%; `Term::op` 22.2% (no mutex; cold node loads), `match_pat` 21.1%, `place` 17.2%, `subst_sig` 14.0% |
| `2026-10-18-sbound-tag-ab` | `bv_base`, `bv_sb`, `bv_both` | `arms_ab.sh 1` | same files; wall 198/200/198 s; join seconds 699/670/639 (contended) |
| `2026-10-18-sbound-tag-quiet` | `bv_base`, `bv_sb`, `bv_both` | `quiet_ab.sh 1 3` (stopped after 2 rounds) | same files; wall 88.0/78.3/77.8 s, job CPU 372/324/321 s |
| `2026-10-18-pcand-salts-record` | `bv_old`, `bv_both` | `salts_ab.sh`, salts 1-10 | M 749 both, every loop equal; wall 1130/954 s, job CPU 7942/6289 s; rules differ in 4 of 30 loops |
| `2026-10-18-aff-index-ab` | `bv_both`, `bv_aff` | `salts_ab.sh`, salts 1-4 | rules and M equal in all 12 loops; bounding 138.2/13.5 s; wall 490/434 s (loaded) |
| `2026-10-18-aff-prof` | `bv_lprof3` | `lazy_prof.sh` | main thread 13.6 k busy samples (25.3 k before), alone 8.9 s; rivals' `score_rule` 52%, `state` 25%, winner loop 12% |
| `2026-10-18-rivals-pool-ab` | `bv_aff`, `bv_riv` | `salts_ab.sh`, salts 1-4 | rules and M equal in all 12 loops; wall 513/475 s (others 48-58%) |
| `2026-10-18-rivals-threads` | `bv_riv` | `threads_check.sh`, salt 5 | rules the same at 6 and 1 threads in all 3 loops |
| `2026-10-18-lview-ab` | `bv_riv`, `bv_lview` (branch `lazy-view`) | `salts_ab.sh`, salts 1-4 | rules and M equal in all 12 loops; wall 432/456 s, job CPU 2963/3211 s (others 40-53%) |
| `2026-10-18-lvprof` | `bv_lvprof` (`lazy-view` + `lazy_prof.patch`) | `lazy_prof.sh` | 523.6 k busy samples; the seen tables' equality (`Reach::same`/`head`) 18.3%, `Term::op` 8.0% |
| `2026-10-18-mainprof` | `bv_mainprof` (2280c01's code + `lazy_prof.patch`) | `lazy_prof.sh` | 485.5 k busy samples; `is_step` 3.1%, `place` 14.9%, `Term::op` 20.6% |
| `2026-10-18-lview2-ab` | `bv_riv`, `bv_lview2` (`lazy-view` 984bde2) | `salts_ab.sh`, salts 1-4 | rules and M equal in all 12 loops; job CPU 3066/3332 s (others 45-70%, uneven) |
| `2026-10-18-lv2prof` | `bv_lv2prof` (984bde2 + `lazy_prof.patch`) | `lazy_prof.sh` | 525.6 k busy samples, join 441 k; `At::same` 15.0% (`At::is` 5.2%, made pattern subterms ~7%) |
| `2026-10-18-mainprof2` | `bv_mainprof` | `lazy_prof.sh`, back to back with `-lv2prof` | 482.0 k busy samples, join 403 k; `is_step` 3.1%, `place` 15.0% |
| `2026-10-18-dup-count` | `bv_dprobe` (645fb11 + `dup_count.patch`) | `match_count.sh`, salt 1 | duplicates 63.6% of candidates, 22.6% of them the predecessor; new terms' spine 1.80, pattern 1.62 nodes; `Term::op` thread-cache hit 74.0%, 77% of misses on a held slot |
| `2026-10-18-cache-ways` | `bv_cways` (645fb11 + `cache_ways.patch`) | `match_count.sh`, salt 1 | shadow caches: 74.0% direct 2^16 (the real count), 77.5% 2-way and 79.7% 4-way at 512 KB, 79.5% at 2^17, 83.2% at 2^18 |
| `2026-10-18-miner-serial-quiet` | `bv_both`, `bv_riv` | `quiet_ab.sh 1 3` (1 clean round by the 3 h deadline) | same files; wall 73.6/58.2 s, job CPU 301/291 s |
| `2026-10-18-interner-ab` | `bv_lazy2`, `bv_lockfree` | `interner_ab.sh`, salt 1 | lock-free 136/140 s against 150/142; rules agree but the first old sweep's loop 15-2 |
| `2026-10-18-size-bound` | `bv_sbound` | `match_count.sh`, salt 1 | the bound skips 43% of matcher calls, 96% of over-cap matches, no match within the cap |
| `2026-10-18-join-paths` | `bv_jpaths` | `join_paths.sh`, salt 1 | met paths: at most 4 uphill steps in 99.8%; deep sides mostly flat steps |
| `2026-10-18-cost-join` | `bv_cjoin` | `cost_join.sh` with `JOIN_SAMPLE_MASK=31`, salt 1 | budget 4: meets 99.9% of real joins and 62% of real failures, at 4.3-8.6 times the terms |
| `2026-10-18-cost-join-ac` | `bv_cjac` | `cost_join.sh` with `JOIN_AC=1 JOIN_SAMPLE_MASK=31 BUDGETS=4`, salt 1 | 1.8 times the terms, but meets only 79% of real joins |
| `2026-10-18-serve-bound` | `bv_sbnd` | `serve_bound_ab.sh`, salts 1-3 | bound in serving: every loop's M and rules unchanged |
| `2026-10-18-exact-salts` | `bv_jexact2` | `exact_salts.sh`, salts 1-10 | `JOIN_EXACT`: M 750 against 749 at +84% wall; rules differ in 28 of 30 loops |
| `2026-10-18-serve-shadow` | `bv_cserve` | `serve_shadow.sh`, salts 1-3 | serving's join failures are exhausted small pairs, none at the visit cap |
| `2026-10-18-snap-salt1` | `bv_snap` | `snap_salts.sh`, salt 1 | a memo per candidate: rules byte-equal at 1 and 6 threads; M 76, 80 s against 93 |
| `2026-10-18-snap-salts` | `bv_snap` | `snap_salts.sh` with `ARMS="base6 snap6"`, salts 1-10 | M 749 in every loop as built, wall -8% (loaded) |
| `2026-10-18-snap-threads` | `bv_snap` | `snap_salts.sh` with `ARMS="snap6 snap1"`, salts 5 7 | rules byte-equal at 1 and 6 threads and across runs |
