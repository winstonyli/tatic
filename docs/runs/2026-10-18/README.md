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
- `scripts/interner_ab.sh <exe A> <exe B> <salt>`: `SWEEP=cold:cmp3d` at 1 lane in the order A B B A, wall seconds, and
  which sweeps' files agree with A's first. A was `bv_lazy2`, B `bv_lockfree` (a49d1af with the lock-free interner).
- `rows/<run id>.txt`: each run's `out.log`; `rows/2026-10-18-lazy-prof.txt` is `prof_named.py`'s table. `rows/lanes-check_cold_l{1,2}_cmp3d_2_mine_0.log`: the first mine of the
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
| `2026-10-18-interner-ab` | `bv_lazy2`, `bv_lockfree` | `interner_ab.sh`, salt 1 | lock-free 136/140 s against 150/142; rules agree but the first old sweep's loop 15-2 |
| `2026-10-18-size-bound` | `bv_sbound` | `match_count.sh`, salt 1 | the bound skips 43% of matcher calls, 96% of over-cap matches, no match within the cap |
| `2026-10-18-join-paths` | `bv_jpaths` | `join_paths.sh`, salt 1 | met paths: at most 4 uphill steps in 99.8%; deep sides mostly flat steps |
| `2026-10-18-cost-join` | `bv_cjoin` | `cost_join.sh` with `JOIN_SAMPLE_MASK=31`, salt 1 | budget 4: meets 99.9% of real joins and 62% of real failures, at 4.3-8.6 times the terms |
