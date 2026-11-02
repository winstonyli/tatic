---
status: done
---

# Context-aware scorer, stages 0 and 1 (offline veto) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Reproduce stage 1's offline signal, dump pool context for 42 mines, and answer Q1: does a context model beat the per-law model and the `small` key at ranking credited laws, leave-one-salt-out.

**Architecture:** A test-only module `ctx_scorer.rs` holds the model (runtime-width standardised logistic fit, recovered from git), the pure feature and statistic functions, and the Q1 report. `miner.rs` gains one env-gated dump (`RULEMINER_POOL_DUMP`) that stores raw per-law facts for the whole pool inside a real arm run; groups 1 to 3 are computed from those facts at load time, so an ablation or layout change never needs a new dump. The served-only cover (for the uncovered flag) is a quiet extraction from `mine`. No kernel change.

**Tech Stack:** Rust test binary `tests/church_bv` (`cargo test`, `--ignored` runs), bash, `run.ps1`. No new dependency.

**Spec:** `docs/superpowers/specs/2026-11-01-context-aware-scorer-design.md` (approved 2026-11-01: m1 strict bar, n1 keep group 3, o1 record-only null; the dump route and the standardisation sentence were corrected 2026-11-01 while planning). Stage 2 (Q2) is out of scope.

## Global Constraints

- Pool = 4n = 1276 laws (n = 319); labelled slice = first n pool laws; y (w1) = `RULEMINER label: 1 <law>`; y = 1 implies straggler. Use `mine_labels` on the first n lines of `laws_extra_<m>.txt` only.
- Every ranker ranks stragglers by score, non-stragglers last in stream order; models fit on labelled stragglers only; no straggler-flag feature. Stage-1 reproduction fits on all rows, as stage 1 did (its TSV has no straggler flag).
- Columns, F = 35: 26 per-law (`per_law_features`); group 1 (3): percentiles of steps, size, fallbacks among the pool's stragglers ((avg rank - 1)/(m - 1), ties share the average, 0.5 when m = 1); group 2 (4), using each law's own two sides as printed and the served stragglers' normal forms: operator-multiset Jaccard (sum min / sum max) of both sides vs the union over the served stragglers; the same for the left side only; fraction of served stragglers whose left-side root operator equals the law's; the same for the right side; group 3 (2): own uncovered flag after the served-only cover (0 for clean laws); fraction of pool stragglers with the same left-side root operator that stay uncovered. A leaf has no root operator and matches nothing.
- "Uncovered" = still a straggler (`fell > 0` or unproved, `classify`) when the pool is classified under the base rules plus the served-only cover's chosen rules.
- Standardise on training rows; the bias column is always kept; a column with sd 0 is omitted from the model and noted. Weights text carries a layout string and `from_text` refuses a mismatch.
- Duplicate law texts: keep the first occurrence (stream order, salts ascending), drop later copies from labelled slices and from fitting, and report the count; leave-one-salt-out groups by salt only. (The cached labels already hold 2 repeats; expect tens at 4x.)
- Gate (m1): at k in {80, 160}, paired bootstrap over the 42 mines (2000 resamples, fixed seed), the 95% interval of d (context minus per-law capture) and of e (context minus `small`) excludes 0 from below, AND d > 0 and e > 0 on at least 5 of 7 salts. Random ranker: mean of 200 shuffles, seeds 1 to 200. `small` order = (steps, size), then stream order, non-stragglers last.
- Reproduction (stage 1): fit salts 4-9, test salt 10: test AUC 0.691, train 0.711, size-only 0.528, each within 0.005; cached labels 13,398 laws / 3,282 credited / 42 mines exactly. Keep the float accumulation order of the stage-1 `fit` when making its width a runtime value.
- Long runs only through `powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind <k> -Name <n> -MaxMemGB 8 -Affinity CFF -Command "..."`; `docs/runs.md` rows stay uncommitted until Task 7's docs commit (`git checkout docs/runs.md` before the code commits would lose them, so stash them aside instead); python only as `python -I -P f.py < /dev/null`; the test exe is built with `cargo test --no-run` and copied outside `target`, paths quoted (the profile path has a space); `bash scripts/tour_check.sh` passes if a tour cite changed; commits end with `Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>`; no push, tag or bump.

## Review Focus

1. A pool with one straggler or none: percentiles give 0.5 and every group column is finite (Task 2).
2. A pool straggler outside the labelled slice has no y and is never fitted on; one inside the slice that no chosen rule covered has y = 0 (Task 6).
3. Duplicate law text across salts or mines is dropped and counted, not fatal (Task 6).
4. Dump on vs off: chosen records and WORK lines are identical (logs differ only by the `ENV RULEMINER_POOL_DUMP` line); the quiet served-only cover adds no `chosen` record to the loop's `rules.txt` (Tasks 3, 4).
5. The `mine` extraction changes nothing observable (Task 3).

---

### Task 1: Recover the model and reproduce stage 1

**Files:**
- Create: `tests/church_bv/ctx_scorer.rs`
- Modify: `tests/church_bv/main.rs` (add `mod ctx_scorer;` to the mod list)

**Interfaces:**
- Produces: `pub struct Model` with `pub fn fit(rows: &[(Vec<f32>, bool)]) -> Model` (rows already filtered by the caller; runtime width; 400 steps, rate 0.5, L2 1e-3, from zero; bias column 0 unstandardised), `pub fn score(&self, x: &[f32]) -> f64`, `pub fn to_text(&self, layout: &str) -> String`, `pub fn from_text(text: &str, layout: &str) -> Result<Model, String>`; `pub fn auc(scored: &[(f64, bool)]) -> f64`; `pub fn per_law_features(law: &(Term, Term)) -> [f32; 26]`; `pub fn mine_labels(extras: &str, log: &str, tag: &str) -> Result<Vec<(String, bool)>, String>`; `pub fn salt_of(path: &str) -> Option<usize>`; ignored tests `dump_labels` and `reproduce_stage1`.

- [ ] **Step 1: Write the failing tests** in `ctx_scorer.rs` (`#[cfg(test)] mod tests`): `auc_of_known_scores` (copy from `git show 8d9ceaf^:tests/church_bv/scorer.rs`), `fit_refuses_no_rows` (`#[should_panic]`), `per_law_features_are_symmetric_finite_and_26_long`, `model_text_round_trips_and_refuses_a_wrong_layout`, `a_constant_column_is_omitted_and_scores_finite`, `mine_labels_refuses_a_log_with_stragglers_and_no_label_line`.
- [ ] **Step 2: Run** `cargo test -j 2 --no-run` build then the tests, through `run.ps1 -Kind probe -Name ctx-t1`. Expected: FAIL (not defined).
- [ ] **Step 3: Implement** by recovering `git show 8d9ceaf^:tests/church_bv/scorer.rs` (`depth`, `consts`, `op_counts`, `features` as `per_law_features`, `fit`, `auc`, `mine_labels`, `salt_of`, `walk`, `dump_labels`), with the runtime-width `Model`. `reproduce_stage1` (ignored, replaces `fit_scorer`): reads `LABELS=<tsv>`, fits all rows of salts 4-9, tests salt 10, asserts the Global Constraints reproduction numbers and the 13,398 / 3,282 / 42 counts.
- [ ] **Step 4: Run** the unit tests. Expected: PASS.
- [ ] **Step 5: Reproduce.** Build the test exe, then `LABEL_DIRS="<claude-runs>/tatic/2026-10-31-v06-labels/s4_A;...;.../s10_A" LABEL_OUT=<scratch>/labels.tsv "<exe>" ctx_scorer::dump_labels --exact --ignored --nocapture` (arm A only: A = B), then `LABELS=<scratch>/labels.tsv "<exe>" ctx_scorer::reproduce_stage1 --exact --ignored --nocapture`. Expected: `LABELS 42 mines, 13398 laws, 3282 credited` and the three AUCs within 0.005. If not, stop and report; do not continue.
- [ ] **Step 6: Commit** `tests: ctx_scorer recovers the stage-1 model with a runtime width; stage-1 AUC reproduced`.

### Task 2: Groups 1 to 3 as pure functions of dumped facts

**Files:**
- Modify: `tests/church_bv/ctx_scorer.rs`

**Interfaces:**
- Produces: `pub fn percentiles(values: &[f64]) -> Vec<f64>`; `pub struct PoolLaw { pub law: (Term, Term), pub straggler: bool, pub steps: i64, pub size: i64, pub fallbacks: u64, pub uncovered: bool }` (steps, size, fallbacks, uncovered meaningful only when `straggler`); `pub fn group1(pool: &[PoolLaw]) -> Vec<[f32; 3]>`; `pub fn group2(pool: &[PoolLaw], served: &[(Term, Term)]) -> Vec<[f32; 4]>` (`served` = the served stragglers' normal forms); `pub fn group3(pool: &[PoolLaw]) -> Vec<[f32; 2]>`; `pub fn row(pool: &[PoolLaw], served: &[(Term, Term)], i: usize) -> Vec<f32>` (the 35 columns of pool law `i`).

- [ ] **Step 1: Write failing tests:** `percentiles_share_the_average_rank_for_ties` (`[1,2,2,3]` gives `[0, 0.5, 0.5, 1]`), `percentiles_of_one_value_is_half`, `group1_is_zero_for_non_stragglers_and_in_unit_range`, `group2_identical_operator_multiset_gives_jaccard_one`, `group2_with_no_served_stragglers_is_zero_not_nan`, `group3_is_zero_for_clean_laws_and_the_uncovered_fraction_otherwise`, `row_is_deterministic_and_35_long_and_finite`, `a_pool_with_no_stragglers_gives_finite_columns`.
- [ ] **Step 2: Run** them. Expected: FAIL (not defined).
- [ ] **Step 3: Implement** the functions; operator multisets via `op_counts` over `OPS`; root operator via the `Node::Op(o, ..)` match of `op_counts`; Jaccard 0 when both multisets are empty.
- [ ] **Step 4: Run** them. Expected: PASS.
- [ ] **Step 5: Commit** `tests: ctx_scorer pool-, served- and marginal-relative features`.

### Task 3: A quiet served-only cover, extracted from `mine`

**Files:**
- Modify: `tests/church_bv/miner.rs`

**Interfaces:**
- Produces: `fn cover(job: &mut Job, laws: &Laws, cfg: &MinerConfig, base: &[(Term, Term)], clock: &Clock, extra: &[(Term, Term)], quiet: bool) -> (Vec<(Term, Term)>, usize)`: everything `mine` does from `candidates(...)` through `rounds.play` and `rounds.report` (the `applicable` filter, `CANDIDATE_CAP`, `Prover::filter`, `Scorer::new`, `Rounds::new`), returning the chosen rules and the rolled-back count; `mine` calls it with `quiet = false` and keeps `job.spent`/`clock.phase` at its level. `quiet = true` skips the `chosen` record (`Rounds::settle`, which `driver::run_loop` appends to `rules.txt`), the `RULEMINER chosen`/`label:`/`uncovered:` lines (`report`) and the candidate-count `println!`s. `fn still_stragglers(job: &mut Job, base: &[(Term, Term)], chosen: &[(Term, Term)], pool: &[(String, Term, Term)], budget: i64, fast: bool) -> Vec<bool>`: installs base + `chosen` as the mined rules (`job.rules().with_mined(job.setup(), ...)`, as `mine` does), runs `classify(.., loud = false)` and reports per pool law whether it is a `Straggler`.

- [ ] **Step 1: Write failing tests** in `miner.rs`: `still_stragglers_with_no_chosen_rules_equals_the_base_stragglers` and `a_chosen_rule_flips_a_straggler_to_covered` (use the fixtures of the existing `served_and_pool`-style miner tests for a law one rule closes), `a_quiet_cover_records_no_chosen_rule` (the `Setup` records of the call contain no `chosen`).
- [ ] **Step 2: Run** them. Expected: FAIL.
- [ ] **Step 3: Implement** `cover` and `still_stragglers`; `mine` becomes `laws` + `cover(.., false)`. Observable behaviour of `mine` unchanged.
- [ ] **Step 4: Verify the extraction is a no-op:** `cargo test -j 2 miner::` passes, and one small real `rule_miner` mine gives the same `chosen` records and `WORK` lines before and after (build both, compare).
- [ ] **Step 5: Commit** `tests: miner cover extracted from mine (quiet mode), still_stragglers`.

### Task 4: The pool dump

**Files:**
- Modify: `tests/church_bv/miner.rs` (`MinerConfig`, `laws_for` and its three callers `laws`, `straggler_names`, the dump)
- Modify: `tests/church_bv/driver.rs` (`run_loop`; header comment documents `POOL_DUMP`)
- Modify: `tests/church_bv/ctx_scorer.rs` (`pool_tsv`, `read_pool`)

**Interfaces:**
- Produces: `MinerConfig.pool_dump: Option<PathBuf>` (`RULEMINER_POOL_DUMP`); `laws_for` takes `&MinerConfig` and `base: &[(Term, Term)]` in place of `guard_k`/`fast` (update its three call sites and the `ExtrasKeep` literal tests); `pub fn pool_tsv(rows: &[(usize, String, Option<(i64, i64, u64)>, bool)]) -> String` (one line per pool law: index, law text, straggler 0/1, steps, size, fallbacks (empty cells for a clean law), uncovered 0/1); `pub fn read_pool(tsv: &str) -> Vec<PoolLaw>`; the served stragglers' normal forms as `served_<m>.txt` (`lhs = rhs` lines). `driver::run_loop` with env `POOL_DUMP` set pushes `RULEMINER_POOL_DUMP=<out>/pool_<name>.tsv` AFTER `let lawfile = env.last()` (so the `append` target stays the law file).

- [ ] **Step 1: Write failing tests:** `pool_tsv_has_one_line_per_law_and_empty_cells_for_clean_laws`, `read_pool_inverts_pool_tsv`.
- [ ] **Step 2: Run** them. Expected: FAIL.
- [ ] **Step 3: Implement.** In `laws_for`'s `First` path, when `cfg.pool_dump` is set: classify all `named` (indices `0..len`, as the `Small` path does), take the served stragglers (`outcomes[..from]`), run `cover(.., quiet = true)` on `assemble(served outcomes, loud = false)` with no extras, call `still_stragglers` on the pool laws, write `pool_<m>.tsv` and `served_<m>.txt`, then cut to the first n and continue exactly as before.
- [ ] **Step 4: Verify** on one small mine: with the dump on vs unset, the `chosen` records and `WORK` lines are identical; the logs differ only by the `ENV RULEMINER_POOL_DUMP` line; the loop's `rules.txt` has no served-only rule; the pool file has `len - from` lines.
- [ ] **Step 5: Commit** `tests: RULEMINER_POOL_DUMP stores raw per-law facts of the classified pool of a first-n mine`.

### Task 5: Probe one salt, then dump all seven

**Files:**
- Create: `scripts/ctx_dump.sh`

- [ ] **Step 1: Write `scripts/ctx_dump.sh <exe> <salts...>`**: per salt, the arm-A sweep of `streams_ab.sh`'s `arm()` alone, without arm B, the table check or the held-out checks: `"$runs" run "$(cygpath -w "$o")" -- MACHINE_STATE=0 SWEEP=cold:streams SALT=$s SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture < /dev/null > "$o/result.txt" 2>&1` into `$RUN_DIR/s${s}_A`; the exe reads `POOL=4`, `EXTRAS_SELECT=first`, `POOL_DUMP=1` from its `<exe>.env` (cached runs used `.exe.env`, e.g. `POOL=1`). The script exits 1 if an arm's `exit` is non-zero or any `mine_*.log` lacks a `RULEMINER label:` line while it reports stragglers.
- [ ] **Step 2: Probe salt 4:** `run.ps1 -Kind probe -Name ctx-dump-s4 -MaxMemGB 8 -Affinity CFF -Command "bash scripts/ctx_dump.sh <exe> 4"`. Expected: under `s4_A`, three loop folders `cold_streams_streams_<l>_none/` each with `pool_0.tsv`, `pool_1.tsv` (1276 lines each), `served_*.txt`, `mine_*.log`. State the duration and peak commit and the estimate for seven salts before the full run.
- [ ] **Step 3: Full dump** salts 4 to 10: `run.ps1 -Kind sweep -Name ctx-dump -Detach ...`, then arm a Bash `until` watcher on `run.json`'s `"end"` with a deadline. Expected: 42 `pool_*.tsv` and 42 `mine_*.log`.
- [ ] **Step 4: Commit** `scripts: ctx_dump.sh runs one arm of the streams sweep with the pool dump` (the run's `docs/runs.md` row waits for Task 7).

### Task 6: Q1 report

**Files:**
- Modify: `tests/church_bv/ctx_scorer.rs`

**Interfaces:**
- Consumes: Tasks 1, 2, 4. Produces: `pub fn capture_at_k(order: &[usize], y: &[bool], k: usize) -> usize`; `pub fn random_capture(y: &[bool], k: usize, seeds: std::ops::RangeInclusive<u64>) -> f64`; `pub fn small_order(pool: &[PoolLaw], slice: usize) -> Vec<usize>` (the `Small` key restricted to the first `slice` laws); `pub fn bootstrap_interval(diffs: &[f64], resamples: usize, seed: u64) -> (f64, f64)`; `pub struct Mine { pub salt: usize, pub name: String, pub pool: Vec<PoolLaw>, pub served: Vec<(Term, Term)>, pub y: Vec<bool> }` (`y` for the first n pool laws); `pub fn load_mines(dirs: &[&Path], n: usize) -> Result<(Vec<Mine>, usize), String>` (mines, dropped-duplicate count); ignored test `q1_report` (env `Q1_DIRS=<arm folder>;..`).

- [ ] **Step 1: Write failing tests:** `capture_at_k_counts_positives_in_the_top_k`, `random_capture_of_all_positives_is_k`, `small_order_matches_kept_indices_semantics` (same tiny pool through `small_order` and through `miner::kept_indices`' rank rule: stragglers by (steps, size), then stream order, rest last), `bootstrap_interval_of_a_constant_positive_sample_excludes_zero`, `bootstrap_is_deterministic_for_a_seed`, `loo_split_never_shares_a_salt`, `load_mines_drops_later_duplicates_and_counts_them`, `load_mines_stops_when_the_first_n_pool_laws_do_not_match_laws_extra`, `load_mines_stops_on_a_repeat_inside_one_mines_own_file`.
- [ ] **Step 2: Run** them. Expected: FAIL.
- [ ] **Step 3: Implement** the functions and `q1_report`: load (labels via `mine_labels` on the first n lines of `laws_extra_<m>.txt`, joined to pool laws by index), for each held-out salt fit the per-law and the context models on the other six (labelled stragglers only), rank each mine's 319 labelled laws with each of the four rankers, and print per k: capture sums of the four rankers, d and e with bootstrap intervals, the per-salt signs, AUC, stragglers and positives per slice, the ceiling min(k, positives), the dropped-duplicate count, the ablation (drop each of groups 1 to 3 and the per-law block) as capture sums, and the verdict `PASS`/`FAIL` per the Global Constraints gate.
- [ ] **Step 4: Run** the unit tests. Expected: PASS.
- [ ] **Step 5: Run** `q1_report` on the Task 5 folders through `run.ps1 -Kind bench -Name ctx-q1`, twice. Expected: the full report, identical output both times.
- [ ] **Step 6: Commit** `tests: ctx_scorer Q1 report (leave-one-salt-out, bootstrap gate)`.

### Task 7: Record the result

**Files:**
- Modify: `docs/tier-cycle.md` (a section beside "A learned scorer over the extras"), `PARKED.md` (stage-2 entry), the spec (status line and verdict), `docs/runs.md` (the Task 5 and 6 rows), `docs/TOUR.md` only if a cite changed

- [ ] **Step 1:** Write the section with run ids, counts (new dump counts, dropped duplicates), the capture table and the verdict; on FAIL say which groups the ablation shows empty; on PASS say Q2 needs its own plan. Update `PARKED.md` (trigger met or not; unify the removed-scorer cite on `8d9ceaf^`).
- [ ] **Step 2:** Docs check: grep `ROADMAP.md`, `PARKED.md`, `docs/tier-cycle.md` for "sees a law in context" wording and fix stale lines; `bash scripts/tour_check.sh` if `TOUR.md` changed (the `miner.rs#mine`, `#laws_of`, `#kept_indices` cites survive the extraction).
- [ ] **Step 3: Commit** `docs: context-scorer Q1 result` and report to the user (Decide: proceed to Q2 only on PASS).
