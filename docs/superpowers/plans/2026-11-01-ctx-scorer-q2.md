---
status: active
---

# Context-aware scorer, stage 2 (Q2, the gate) Implementation Plan

> **For agentic workers:** execute inline (`superpowers:executing-plans`) unless the user says otherwise: Tasks 4 to 7 are sequential runs that depend on each other. Steps use checkbox (`- [ ]`) syntax. Set `status: active` when Task 1 starts.

**Goal:** Answer Q2: does ranking each mine's pool of extras with the context model (33 columns, no marginal-coverage group) lower held-out M below the `small` key at the same n, without more mining work, on salts the model never saw?

**Architecture:** `EXTRAS_SELECT=ctx` is a third `Keep` in `laws_for`. It shares `Keep::Small`'s path (classify the pool, rank the stragglers, `kept_indices`, the same report lines); only the rank differs: the model's score over `ctx_scorer`'s runtime columns instead of (steps, size). The pool facts (`PoolLaw` per pool law) come from one builder shared with `dump_pool`, so the model sees at runtime what it was fit on. The model is fit offline by an ignored test on the stage-0 dump and read by the miner from a text file. The gate is `scripts/streams_ab.sh` arm pairs (A = `small`, B = `ctx`) judged by a pre-registered rule in `scripts/q2_verdict.sh`. Nothing in the kernel changes; no score reaches the kernel.

**Tech Stack:** Rust test binary `tests/church_bv`, bash/awk, `run.ps1`, `streams_ab.sh` with `gate.sh`. No new dependency.

**Spec:** `docs/superpowers/specs/2026-11-01-context-aware-scorer-design.md` (stage 2, as amended). Q1 result: `docs/tier-cycle.md`, "A context model over the extras: the offline veto".

## Global Constraints

- Decisions (2026-11-01): c1 = 33 columns, group 3 (marginal coverage) dropped, so no served-only cover at runtime and no `mine_served_only` refactor; d1 = pool 4 (`POOL=4`), n in {80, 160}; Q1's bar was amended to k in {40, 80} (a2).
- Long runs only through `powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind <k> -Name <n> -Affinity CFF [-Detach] -Command "bash <8.3 path to a script>"` (a script, because env variables cannot be set inline in `-Command`). Gates: `-Kind gate -MaxMemGB 24` (the job object caps the whole tree: 3 concurrent arms plus held-out checks; each arm keeps `streams_ab.sh`'s 8 GB watchdog; after the first gate read `peak_commit_mb` in `run.json` and set the cap from it); fit and Q1 probes: `-MaxMemGB 8`. A gate's command is `bash C:/Users/WINSTO~1/DOCUME~1/GitHub/tatic/docs/runs/2026-10-31/scripts/gate.sh <exe A> <exe B> <salts>` (8.3 paths). A detached run gets a watcher (`until` loop on `run.json`'s `end`, with a deadline). Check `Get-Process` for orphans before and after; python only as `python -I -P f.py < /dev/null`.
- The gate exes are a **release** build: `cargo test --release -j 2 --test church_bv --no-run`, copy the printed executable to `%LOCALAPPDATA%\claude-runs\tatic\q2-exes\base.exe` (the `[profile.test]` build has debug assertions and replays every memo hit, so its CPU and watchdog readings would not match any recorded arm). Unit tests and the ignored Q1/fit reports may use the default test build.
- Defender real-time protection state is logged with every gate (`run.json` conditions). Gates are untimed counts: the verdict rests on held-out M and WORK counts (deterministic), job CPU is a cross-check (about +-10% load noise).
- Arms are exe copies plus `<exe>.exe.env` in `q2-exes` (the `v06-exes` convention). `ARM_CACHE` hashes the exe and its `.env` but not files the `.env` names, so a weights file is write-once: `ctx_fit` refuses an existing `FIT_OUT`, a refit gets a new name. Weights files live in `docs/runs/2026-11-01/ctx-weights/` and are committed.
- Commits are small and topical, use explicit pathspecs (never `git add -A`, never stash or checkout `docs/runs.md`: its wrapper rows stay uncommitted until Task 8), end with `Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>`, and follow `git diff --stat`. No push, tag or bump. `bash scripts/tour_check.sh` passes in the commit that changes a tour cite.
- Unit-test loop: `cargo test -j 2 -- <filter> [<filter>]`; the full `cargo test -j 2` at Task 3 and at Task 8.
- "The record" below means the "Q2" section of `docs/tier-cycle.md` (created at Task 6 step 1; each run task appends its numbers and run ids and commits).

## Reading a result (set before the data)

- c1 (33 columns) was chosen after the Q1 numbers, including the ablation, were seen: a forking path the record states. Task 1 re-runs Q1 on the 33-column model; a FAIL there is a live outcome (the ablation keeps about half of the context model's lead over per-law), and its Decide group is pre-written in Task 1.
- The rule needs the context arm to beat `small` by more than max(76, S), about 1.4% to 1.6% of held-out M (4,700 to 5,400), on four conditions at once, while the plausible effect is what Q1's capture gain implies (context over a random order of stragglers +11% at k = 80, `small` +3%): small. A null therefore means "no effect of at least T held-out M detected at pool 4", never "no context signal". The Q2 record says so, and so does the `PARKED.md` sentence.
- The deterministic gate has no A/A: a rerun reads zero spread; S is the `GEN_DRAW` redraws of `small` only, a two-draw estimate. D itself has unmeasured draw-to-draw noise, so ctx is also redrawn at draws 3 and 4 (arms `c<n>_<w>_d<d>`); the verdict stays the pre-registered rule at draw 0, and the record reports D at all three draws ("D < -T at k of 3 draws") as a robustness read, not a second verdict.
- The work cap can fail ctx by construction (it may prefer dearer credited stragglers than `small`'s fewest-steps). `q2_verdict.sh` prints D and R separately, and the record shows the equal-work random difference beside each verdict (as in the knee chart), so a work-only FAIL is visible as such. The random arms (equal work and redraws) are for that comparison and for the random spread; they do not enter the verdict.
- Two shifts the plan cannot remove, stated in the record: (1) the model is fit on labels of n = 319 mines and ranks pools at n = 80 and 160, where fewer extras compete for each rule; (2) the dump's base rules come from a random n = 319 arm, while the Q2 mines run under rules mined from 80 or 160 extras, so which laws are stragglers, and their steps and sizes, differ. Replication (same n, same kind of model) tests neither, and the salts 4-6 replication is not independent of the choices of feature set and Q1 bar, which were made on results over salts 4-10. A direct check (repeat the stage-0 dump at `EXTRAS_N` 80 and 160 and refit on those labels) is not in this plan; it is the follow-up if Q2 is null.

## Review Focus

- A weights file with another layout or width, a missing or unreadable file, or `EXTRAS_SELECT=ctx` without `CTX_WEIGHTS`: the mine refuses with a message naming `RULEMINER_CTX_WEIGHTS` (Task 3).
- Train/serve skew: the model is fit on `rows()` of the dump's `PoolLaw`s, but the miner builds them itself; a wrong sign, a rank offset by `from`, or a drifting builder passes unit tests of the parts (Task 3 parity and direction tests).
- A pool with fewer stragglers than n, or none: `ctx` fills the shortfall in stream order as `small` does; with no surplus ctx and `small` choose the same set, so the record reports how many mines have any surplus (Task 2, Task 4, Task 6).
- NaN or tied scores (an all-zero model): ranks stay a total order, ties in stream order (Task 2).
- A stale `ARM_CACHE` hit after a weights change, or a verdict over mismatched salt sets after an arm failed (Task 4, Task 5).

## File structure

- `tests/church_bv/ctx_scorer.rs` (modify): `LAYOUT`, `NO_G3`, `runtime_cols`, `runtime_rows`, `ctx_ranks`, `fit_model`, `Model::width`, `overlap`, the `ctx_fit` and `overlap_report` ignored tests, `q1`'s `context` argument.
- `tests/church_bv/miner.rs` (modify): `Keep::Ctx`, `MinerConfig.ctx_weights`, `pool_laws` (the shared `PoolLaw` builder), the `rank` closure of `laws_for`.
- `tests/church_bv/driver.rs` (modify): `extras_select` accepts `ctx`; `ctx_weights`; `CTX_WEIGHTS` becomes `RULEMINER_CTX_WEIGHTS`.
- Architecture note for the close: `Keep` grows a third kind (the tripwire), but `Ctx` shares `Small`'s whole path and differs only in the rank closure. If Q2 is null, `Keep::Ctx`, `RULEMINER_CTX_WEIGHTS`, `ctx_fit`, `q2_arms.sh` and the weights files stay parked (the entry names them), or are deleted on the user's call; Task 8 puts that to the user as a Decide group.
- `scripts/ctx_q1.sh`, `scripts/ctx_overlap.sh`, `scripts/ctx_fit.sh`, `scripts/q2_arms.sh`, `scripts/q2_arms_check.sh`, `scripts/q2_verdict.sh`, `scripts/q2_verdict_check.sh` (create).
- Docs: spec (decisions, stale lines), `docs/tier-cycle.md`, `PARKED.md`, `docs/TOUR.md`, `docs/runs.md`, this plan's status.

---

### Task 0: Commit the plan and the spec amendments

- [ ] **Step 1:** The edits are already in the working tree: check by grep that `PARKED.md` points at this plan (not "its own plan"), and that the spec has the plan pointer at line 17, the "Amended 2026-11-01 after Q1" paragraph (a2, c1, d1) under Decisions, the reworded TOUR condition and the "not built (decision c1)" note on `mine_served_only`. Fix only what is missing.
- [ ] **Step 2:** `git diff --stat`, then commit the plan, the spec and `PARKED.md` by pathspec (`docs: Q2 plan; spec amendments c1, d1, a2`).

### Task 1: Q1 gate for the 33-column model

The choice c1 rests on the 33-column model still clearing Q1's bar; this task computes it (the ablation so far printed capture sums only).

**Files:**
- Modify: `tests/church_bv/ctx_scorer.rs` (`q1`, `q1_report`, tests)
- Create: `scripts/ctx_q1.sh`

**Interfaces:**
- Consumes: `variants() -> Vec<(&'static str, Vec<usize>)>` (the entry `"drop group 3"` is the 33-column model), `Mine`, `load_mines`.
- Produces: `pub const NO_G3: &str = "drop group 3"`; `pub fn q1(mines: &[Mine], ks: &[usize], context: &str) -> String`: `context` names the `variants()` entry that plays the "context" role (table, d, e, gate, verdict). Implementation: look the name up in `variants()` (panic naming it if absent) and swap that entry to index 0, so per-law stays at index 1 and every variant, including a plain `context` row, stays in the ablation line. A new first line `context model: <name> (<cols> columns)`. `q1_report` reads `Q1_CONTEXT` (default `"context"`). `scripts/ctx_q1.sh <exe> [context-key]` takes a space-free key (`full` = "context", `no-g3` = `NO_G3`; default `no-g3`), exports `Q1_CONTEXT` with the mapped name itself (no spaces cross `run.ps1 -Command`), runs the report on the seven `2026-11-01-ctx-dump/s<salt>_A` folders and writes the last `verdict`/`gate met` lines to `$RUN_DIR/headline.txt`.

- [ ] **Step 1: Write the failing tests** in `ctx_scorer::tests`: `q1_header_names_the_context_variant` (`q1(&mines, &[3], "context")` contains `context model: context (35 columns)`; with `NO_G3`, `context model: drop group 3 (33 columns)`); `q1_context_report_apart_from_the_header_equals_the_old_report` (strip the first line; the rest equals a string literal captured from the synthetic fixture before the change); `q1_refuses_an_unknown_variant` (`#[should_panic(expected = "bogus")]`).
- [ ] **Step 2: Run** `cargo test -j 2 -- ctx_scorer::tests::q1`. Expected: FAIL (signature).
- [ ] **Step 3: Implement** as above; existing callers pass `"context"`.
- [ ] **Step 4: Run** `cargo test -j 2 -- ctx_scorer`. Expected: all pass.
- [ ] **Step 5: Run the report** (`run.ps1 -Kind probe -Name q2-t1 -MaxMemGB 8 -Command "bash C:/Users/WINSTO~1/.../scripts/ctx_q1.sh <8.3 path of copied test exe> no-g3"`). Expected: `LOADED 42 mines`, `verdict PASS` and `gate met at k in [40, 80]` in the headline. **A FAIL is a live outcome: stop**, record the numbers in `docs/tier-cycle.md` and put this Decide group to the user: (1) stop at Q1, group 3's over-credit makes the 35-column model an unfair arm (cost: nothing built); (2) build `mine_served_only` and run the 35-column model (cost: a miner refactor and a partial mine per mine in CPU, and the 5% work cap is at risk); (3) amend the bar again (a forking path; weakest).
- [ ] **Step 6: Record** a bullet "Q2 feature set gate" under the Q1 section of `docs/tier-cycle.md` (run id, d and e with intervals at both k, per-salt counts, capture sums); commit code, script and bullet together.

### Task 2: Runtime features, ranks and the fit

**Files:**
- Modify: `tests/church_bv/ctx_scorer.rs`

**Interfaces:**
- Consumes: `PoolLaw`, `per_law_features`, `group1`, `group2`, `rows`, `score_order`, `fit`, `Model`, `Mine`, `load_mines`, `NO_G3`.
- Produces:
  - `pub const LAYOUT: &str = "ctx33-v1"`; `pub fn runtime_cols() -> Vec<usize>` (the columns of the `NO_G3` variant; `variants()` takes that entry from it).
  - `Model::width(&self) -> usize`.
  - `pub fn runtime_rows(pool: &[PoolLaw], served: &[(Term, Term)]) -> Vec<Vec<f32>>`: the 33 columns per pool law, computed without group 3.
  - `pub fn ctx_ranks(scores: &[f64], straggler: &[bool]) -> Vec<Option<i64>>`: `Some(position)` of each straggler in descending-score order (ties in stream order, via `score_order` with every law live), `None` for the rest; indexed from 0 over the slice it is given.
  - `pub fn fit_model(mines: &[Mine], salts: &[usize]) -> Model`: fit on the live labelled stragglers of the mines whose salt is in `salts`, over `runtime_rows`; panics naming the salts if there is no such row.
  - Ignored `ctx_fit` (env `Q1_DIRS`, `FIT_SALTS` like `4-10`, `FIT_OUT`): loads the 42 mines, refuses an existing `FIT_OUT`, prints the row count, the train AUC and `dropped()`, writes `fit_model(..).to_text(LAYOUT)`.

- [ ] **Step 1: Write the failing tests**: `runtime_rows_equal_rows_projected_on_runtime_cols` (synthetic pool, `uncovered` set both ways); `runtime_cols_has_33_columns_and_no_group3` (`len() == WIDTH - 2`, contains 0, none of the last two indices); `ctx_ranks_orders_stragglers_by_score_and_leaves_the_rest_none` (scores `[0.1, 5.0, 3.0, 9.0]`, straggler `[true, true, false, true]` gives `[Some(2), Some(1), None, Some(0)]`); `ctx_ranks_of_equal_scores_is_stream_order`; `ctx_ranks_survives_nan` (no panic, distinct ranks); `fit_model_uses_only_the_named_salts_and_refuses_none` (the model for salt 1 equals `fit` on that salt's rows; `#[should_panic(expected = "salts")]` for `&[99]`); `model_width_is_the_fitted_width`.
- [ ] **Step 2: Run** `cargo test -j 2 -- ctx_scorer::tests`. Expected: FAIL (not defined).
- [ ] **Step 3: Implement** the items; `runtime_rows` is `per_law_features` + `group1` + `group2` per law; `ctx_ranks` reuses `score_order`.
- [ ] **Step 4: Overlap helper, test first.** `pub fn overlap(train: &[&Path], train_slice: usize, eval: &[&Path]) -> (usize, usize)`: how many distinct law texts of the eval folders' `laws_extra_*.txt` (the whole pool, all arms and draws) also occur in the first `train_slice` lines of the train folders' `laws_extra_*.txt`, and the number of distinct eval texts (exact text; alpha-renamed twins are not counted, the same measure as the recorded 0.04% base rate). Test `overlap_counts_shared_law_texts_in_the_train_slice_only` (a train law past the slice is not counted; one shared law of two eval texts gives `(1, 2)`). Ignored `overlap_report` (env `TRAIN_DIRS`, `EVAL_DIRS`, `TRAIN_SLICE` default 319) prints the pair and the percentage; `scripts/ctx_overlap.sh <exe> <train dirs> <eval dirs>` runs it.
- [ ] **Step 5: Run** `cargo test -j 2 -- ctx_scorer`. Expected: all pass.
- [ ] **Step 6: Commit** (`tests: ctx_scorer runtime columns, ranks, fit and overlap for Q2`).

### Task 3: `Keep::Ctx` in the miner and the driver

**Files:**
- Modify: `tests/church_bv/miner.rs` (`Keep`, `Keep::parse`, `MinerConfig`, `laws_for`, `dump_pool`; tests beside `the_pool_is_cut_by_the_stragglers_verdict`; the helper `straggler_names*`)
- Modify: `tests/church_bv/driver.rs` (`extras_select`, `ctx_weights`, the env forwarding beside `RULEMINER_EXTRAS_BY`, the header comment)
- Modify: `docs/TOUR.md` (the `miner.rs` and `ctx_scorer.rs` lines gain `Keep::Ctx`, `CTX_WEIGHTS`)

**Interfaces:**
- Consumes: `ctx_scorer::{runtime_rows, runtime_cols, ctx_ranks, LAYOUT, PoolLaw, rows}`, `Model::{from_text, score, width}`, `kept_indices`, `Outcome`.
- Produces: `Keep::Ctx`, `Keep::parse("ctx")`; `MinerConfig.ctx_weights: Option<String>` from `RULEMINER_CTX_WEIGHTS`; `fn pool_laws(named: &[(String, Term, Term)], outcomes: &[Outcome], from: usize) -> (Vec<PoolLaw>, Vec<(Term, Term)>)` (the pool's `PoolLaw`s with `uncovered: false`, and the served stragglers' normal forms; `dump_pool` uses it too, so the dump and the runtime cannot drift); driver `fn ctx_weights(select: Option<&str>, weights: Option<&str>) -> Result<Option<String>, String>`; the helper `straggler_names_with(text, extras, weights: Option<&str>)` (sets `RULEMINER_CTX_WEIGHTS`).

- [ ] **Step 1: Write the failing tests.** `miner.rs`: `keep_parses_ctx_and_names_the_variable_on_error`; `a_ctx_pool_with_a_zero_model_keeps_the_straggler_like_small` (the `served_and_pool` fixture, a hand-written zero model `layout ctx33-v1\nwidth 33\nkeep 0\nmean 0\nscale 1\nw 0\n`, redefine the local `ex` closure); `ctx_without_weights_names_the_variable` (`#[should_panic(expected = "RULEMINER_CTX_WEIGHTS")]`); `ctx_refuses_a_missing_weights_file` (same expectation); `ctx_refuses_a_weights_file_of_another_layout` (`expected = "layout"`); `ctx_refuses_a_weights_file_of_another_width` (a valid 5-wide model; expectation names `RULEMINER_CTX_WEIGHTS`); `ctx_with_n_zero_reads_no_extra`; `ctx_pool_facts_equal_the_dump_rows` (parity; `laws_for` returns `Laws`, not pool facts, so the test calls `classify` and `pool_laws` itself under a `Job`, as `served_and_pool` does, writes the dump TSV through `dump_pool`, `read_pool`s it back and compares every cell of `ctx_scorer::rows` with `runtime_rows` over `pool_laws`' output, on the columns of `runtime_cols`); `ctx_follows_the_model_not_the_steps` (the new fixture `pool_with_stragglers()`: at least 3 pool stragglers of distinct (steps, size), picked from the existing law lists in `miner.rs` tests and asserted to classify as `Outcome::Straggler` before use; with one straggler every percentile is 0.5 and the test would pin nothing; a hand-written one-feature model on the steps-percentile column: with a positive weight the highest-step straggler is kept at n = 1, with a negative weight the lowest; this pins the sign and the `from` offset); `ctx_reports_how_many_kept_differ_from_small` (the same fixture: the report line `RULEMINER extras ctx-vs-small: <d> of <k> kept differ` has d = 0 when the model is the steps-percentile column with a negative weight, d > 0 with a positive one). `driver.rs`: `extras_select_accepts_ctx`; `ctx_weights_needs_ctx_and_ctx_needs_weights` (`ctx` without weights errs naming `CTX_WEIGHTS`; weights without `ctx` errs).
- [ ] **Step 2: Run** `cargo test -j 2 -- miner:: driver::extras driver::ctx`. Expected: FAIL.
- [ ] **Step 3: Implement.** `Small` and `Ctx` share one path in `laws_for` (classify, `rank`, `kept_indices`, the report lines, unchanged text); only the `rank` closure differs. For `Ctx`: `pool_laws` gives the facts, scores are `model.score(&row)` over `runtime_rows`, `ranks = ctx_ranks(&scores, &straggler)` over the pool slice, and `rank(i) = ranks[i - from].map(|p| (p, 0))` (`kept_indices` asks pool indices only, absolute). The model is read once per mine; every failure panics naming `RULEMINER_CTX_WEIGHTS` (and `layout` for a layout error; width is checked against `runtime_cols().len()`). In the `Ctx` path also compute `small`'s choice from the same outcomes and print `RULEMINER extras ctx-vs-small: <d> of <k> kept differ` (d = kept pool laws not in `small`'s set). `dump_pool` builds its `pool_tsv` row tuples from `pool_laws`' `PoolLaw`s plus `uncovered` from `still_stragglers`, so the dump and the runtime share one builder. Driver (`driver.rs`): call `ctx_weights(setup.var("EXTRAS_SELECT"), setup.var("CTX_WEIGHTS"))?` in `scope_extras` (a missing file or variable fails the sweep early, not as a mine panic); in `run_loop` push `("RULEMINER_CTX_WEIGHTS", path)` beside `RULEMINER_EXTRAS_BY`, inside the same `if let Some(by)` block; update the `Keep::parse` error, the `extras_select` messages (`first|small|ctx`) and the header comment, and the existing test that asserts the `Keep::parse` error text.
- [ ] **Step 4: Update `docs/TOUR.md`** and run `bash scripts/tour_check.sh`.
- [ ] **Step 5: Run** the filters, then the full `cargo test -j 2`. Expected: all pass (record the count).
- [ ] **Step 6: Commit** (`tests: EXTRAS_SELECT=ctx ranks the pool by the context model`), code and tour together.

### Task 4: Weights, arms and smoke

**Files:**
- Create: `scripts/q2_arms.sh`, `scripts/q2_arms_check.sh`, `docs/runs/2026-11-01/ctx-weights/ctx33-v1-s4-10.txt`, `ctx33-v1-s7-10.txt`, a fit script `scripts/ctx_fit.sh <exe> <salts> <out>`

**Interfaces:**
- Produces: `scripts/q2_arms.sh <test exe> <out dir> [m...]` writes, per arm, `<out dir>/<name>.exe` and `<name>.exe.env`: `s<n>_d<d>` (`EXTRAS_N=<n> POOL=4 EXTRAS_SELECT=small`, plus `GEN_DRAW=<d>` when d > 0), `c<n>_<w>` and `c<n>_<w>_d<d>` for d in {3, 4} (`EXTRAS_N=<n> POOL=4 EXTRAS_SELECT=ctx CTX_WEIGHTS=<path>`, plus `GEN_DRAW=<d>`), `r<m>_d<d>` (`EXTRAS_N=<m>`, plus `GEN_DRAW` when d > 0), for n in {80, 160}, w in {4-10, 7-10}, d in {0, 3, 4}, m from the arguments. The weights path is `cygpath -m "$(cygpath -d <repo weights file>)"`; the script fails if the file is missing or the path has a space.

- [ ] **Step 1: Write the failing check** `scripts/q2_arms_check.sh` (dummy exe and dummy weights files in a temp dir): `c80_4-10.exe.env` holds `EXTRAS_SELECT=ctx` and a `CTX_WEIGHTS` line without a space; `r208_d3.exe.env` holds `EXTRAS_N=208` and `GEN_DRAW=3`; `s80_d0.exe.env` has no `GEN_DRAW`; a missing weights file fails the script. Run: FAIL (script missing).
- [ ] **Step 2: Implement** `q2_arms.sh`; rerun the check. Expected: pass.
- [ ] **Step 3: Fit both weights** under `run.ps1 -Kind probe -Name q2-fit -MaxMemGB 8 -Command "bash .../scripts/ctx_fit.sh <exe> 4-10 <path>"` then `7-10` (`ctx_fit.sh` sets `Q1_DIRS`, `FIT_SALTS`, `FIT_OUT` and runs `ctx_scorer::ctx_fit --exact --ignored --nocapture`). Expected: row counts printed (4-10: the live labelled stragglers of Q1, 4,728; 7-10: fewer), train AUC above 0.65; the `dropped()` list goes in the commit message.
- [ ] **Step 4: Build** the release exe (Global Constraints), run `q2_arms.sh`, then the smoke gate `gate.sh s80_d0.exe c80_4-10.exe 1` (`-Kind gate -Name q2-smoke -MaxMemGB 24`). Expected: `0 of 2 arms failed`; the ctx arm's `out.txt` shows `CTX_WEIGHTS` among its `ENV` lines; its `mine_*.log` `RULEMINER extras ctx-vs-small:` lines show a nonzero `<d>` in at least one mine (a silent all-ties fallback or a dropped-column model would give d = 0 everywhere; step sums across arms are not comparable, since later mines of a loop run under different base rules, and the first mine has no rules so every step is 0); `rules differ` in at least one loop. Record, per mine, pool stragglers minus n (from the `extras:` line) and how many mines have any surplus: with none, ctx and `small` choose the same set.
- [ ] **Step 5: Commit** scripts and weights (`scripts: Q2 arm builder and fit; ctx weights fit on salts 4-10 and 7-10`).

### Task 5: The pre-registered rule as a script

**Files:**
- Create: `scripts/q2_verdict.sh`, `scripts/q2_verdict_check.sh`

**Interfaces:**
- Consumes: `streams_ab.sh` logs: `total A:` / `total B:` lines carry `held <H>` and `walk=<W>`; the last line ends `<k> of <a> arms failed`.
- Produces: `scripts/q2_verdict.sh <label> <ctx gate log> <small draw 3 log> <small draw 4 log>`. The ctx log has A = `small` draw 0, B = `ctx`; the redraw logs have A = `small` at draws 3 and 4 (B ignored). Each log must end `0 of <a> arms failed` with the same `<a>` in all three, else exit 2 with no verdict line. Prints `<label>: small <H0> walk <W0>; ctx <Hc> walk <Wc>; spread <S>; threshold <T>; held diff <D>; work ratio <R>; PASS|FAIL` with S = max(|H3 - H0|, |H4 - H0|), T = max(76, S), D = Hc - H0, R = Wc / W0; PASS iff D < -T and R <= 1.05. Exit 0 with a line, 2 on a malformed or failed log. Mode `q2_verdict.sh --d-only <label> <gate log> <T>`: A and B of one log are small and ctx at the same draw; prints `<label>: D <D>; work ratio <R>; D < -T: yes|no` (same log checks, no spread rule).

- [ ] **Step 1: Write the failing check** `q2_verdict_check.sh` (fixture logs inline): a pass (H0 5000, Hc 4800, spreads 30 and 50, walks 100 and 104); a held-out fail (Hc 4950); a work fail (walks 100 and 106); a spread case (draws give S = 90 so T = 90 and D = -80 is a FAIL); a log ending `2 of 6 arms failed` (exit 2, no line); mismatched arm counts across logs (exit 2); `--d-only` on the pass fixture prints `D -200` and `D < -T: yes` for T = 76, and `no` for T = 250.
- [ ] **Step 2: Implement** with awk; rerun. Expected: pass.
- [ ] **Step 3: Commit** (`scripts: Q2 verdict rule`).

### Task 6: Primary run (salts 1-3, weights from salts 4-10)

**Files:** none (runs; the record in `docs/tier-cycle.md`)

- [ ] **Step 1: Context and small gates**, n in {80, 160}: `gate.sh s<n>_d0.exe c<n>_4-10.exe 1 2 3` (`-Kind gate -Name q2-p-c<n> -MaxMemGB 24`). Expected `0 of 6 arms failed`. For n = 160 the `small` arm is the regression check of the shared `Small`/`Ctx` path: it must read held-out M 4690 and walk 490 M (match 3.12 G, op 1.60 G; `docs/tier-cycle.md`, "A key under an empty base"); a different count means the refactor changed `small`: stop. Create the Q2 section of `docs/tier-cycle.md` with these numbers and the surplus counts, and commit.
- [ ] **Step 2: Overlap check, before any verdict.** `scripts/ctx_overlap.sh` with train = the ctx-dump `s4`-`s10` folders and eval = this task's `s1`-`s3` arm folders (every `laws_extra_*.txt`), through `run.ps1 -Kind probe -MaxMemGB 8`. Pre-registered: more than 1% of eval texts in the train slice stops the verdict and is reported to the user. Compare with the train folders against each other (5 repeats in 13,398 labelled laws, 0.04%, `docs/tier-cycle.md`). Record the rate in the Q2 section.
- [ ] **Step 3: Equal-work random.** The `r<m>` arms are built on demand: before each random gate re-run `q2_arms.sh <exe> q2-exes <m>` for the m about to be used (Task 4 builds none), again after a correction, and once more for the final m so the d3 and d4 arms of step 4 exist. First guess m0: interpolate between the knee chart's verified random-arm walks on salts 1-3 (n 208: about 219 M, n 433: about 488-545 M, n 700: about 780-784 M; `docs/tier-cycle.md`, knee chart; walk is about 1.05-1.13 M per n) to the ctx arm's walk; run `gate.sh r<m0>_d0.exe c<n>_4-10.exe 1 2 3`; one correction round by linear interpolation between the two nearest measured points if the random walk is off by more than 5%; if still off, report the actual walk ratio and interpolate held-out M to equal work. Report the held-out difference as in the knee chart.
- [ ] **Step 4: Redraws**: for d in {3, 4} and both n, `gate.sh s<n>_d<d>.exe r<m>_d<d>.exe 1 2 3` (A gives `small`'s redraw, B the random redraw for the knee-chart comparison).
- [ ] **Step 4b: ctx redraws** (like with like): for d in {3, 4} and both n, `gate.sh s<n>_d<d>.exe c<n>_4-10_d<d>.exe 1 2 3` (the `s<n>_d<d>` arms are cached from step 4); then `q2_verdict.sh --d-only <label> <log> <T>` with T from the draw-0 verdict, giving D = H(ctx, d) - H(small, d) and R at that draw (robustness read only, not re-judged by the four-term rule).
- [ ] **Step 5: Verdict** (only after step 2 passed): `q2_verdict.sh primary-n<n> <ctx gate log> <d3 log> <d4 log>` per n; append to the record the verdict lines, the random-equal-work difference beside each, the mean "extras selection" phase time of ctx against `small` (the scoring cost; walk counts do not include it), and the job CPU. About 8 to 10 gates, 5 to 18 minutes each at `JOBS=3`.

### Task 7: Replication (salts 4-6, weights from salts 7-10)

**Files:** none

- [ ] **Step 1:** Repeat Task 6 steps 1, 3, 4 and 4b on salts 4 5 6 with `c<n>_7-10.exe`. The `small` n = 160 arm must read held-out M 4591 and walk 533 M (`docs/tier-cycle.md`, "A key under an empty base"). For the equal-work random start from Task 6's measured points (salts 4-6 walk 5-10% above salts 1-3's), then the same correction round.
- [ ] **Step 1b: Overlap check** as in Task 6 step 2, eval = the `s4`-`s6` arm folders, train = the `s7`-`s10` ctx-dump folders (the fit set of this arm); the same stop rule. Also run it against the `s4`-`s10` train set and report it, since the Task 6 weights saw salts 4-6.
- [ ] **Step 2:** `q2_verdict.sh replication-n<n> ...` per n (only after step 1b passed); append to the record.
- [ ] **Step 3: Pre-registered reading:** the context arm passes Q2 iff all four verdict lines (primary and replication, both n) read PASS. A mixed result is reported as mixed, not rounded.

### Task 8: Docs and close

**Files:**
- Modify: `docs/tier-cycle.md`, `PARKED.md`, `ROADMAP.md`, `docs/learned-vs-fixed.md`, `docs/TOUR.md` (only if a cite changed), the spec (result note), this plan (`status: done`), `docs/runs.md`

- [ ] **Step 1: Docs.** `docs/tier-cycle.md`: finish the Q2 section (the four verdict lines and D at the three draws, random-equal-work differences, work and job CPU, scoring time, surplus counts, the overlap rates, the two shifts, the forking-path note and the power statement from "Reading a result", run ids) and add a pointer from the Q1 section ("Q2 would rank the whole pool"). `PARKED.md`: replace only the Q2 sentence inside the existing "Learned proposer, stage 2 ..." entry with the result and run ids; its status stays `parked` (decision o1: a null is recorded only). `ROADMAP.md` (the "No milestone is open ... selection by small" line) and `docs/learned-vs-fixed.md`: update if the result changes them. `docs/TOUR.md` and `bash scripts/tour_check.sh` if a cite changed. Spec: a result note under Stage 2. Grep `PARKED.md`, `ROADMAP.md`, `docs/tier-cycle.md`, `docs/learned-vs-fixed.md` and the spec for "its own plan", "(Q2)", "not yet written" and "selection by small", and say which files were fixed or stale. Plan `status: done`.
- [ ] **Step 2: Full `cargo test -j 2`**, `git diff --stat`, commit docs and `docs/runs.md` rows by pathspec (`docs: Q2 result`).
- [ ] **Step 3: Closing report** per the user's Message format. The Architecture check names `Keep`'s third kind (shared path, rank closure only). If Q2 is null, put this Decide group: (1) keep `Keep::Ctx`, `RULEMINER_CTX_WEIGHTS`, `ctx_fit`, `q2_arms.sh` and the weights parked, named in the `PARKED.md` entry (cheaper to revive, leaves a special case in the dispatcher); (2) delete them, keeping the record (end-state design; recoverable from git); (3) the direct check named under "Reading a result" (stage-0 dump at `EXTRAS_N` 80 and 160, refit).
