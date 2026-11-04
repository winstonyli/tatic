---
status: active
---

# Move `tatic` to `crates/tatic` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans (the user chose inline execution for SR4;
> confirm for this plan). Steps use checkbox syntax.

**Goal:** `src/`, `tests/`, `benches/` and the package manifest of `tatic` move to `crates/tatic`; the root becomes a
virtual workspace; behaviour is unchanged.

**Architecture:** one rename-only commit, one manifest commit, one commit for code and script path fixes, one for docs,
then the checks. Between the first and second commit the tree does not build; that is intended and ledgered.

**Tech Stack:** Cargo workspace, bash, `~/.claude/runs/run.ps1`, `~/.claude/samply/icount.ps1`.

**Spec:** `docs/superpowers/specs/2026-11-04-tatic-crate-move-design.md`

## Global Constraints

- Package name stays `tatic`; bins `demo` and `repl`, test targets, bench names unchanged; test list stays 749 names.
- `[profile.sweep]` and `[profile.test]` stay in the root manifest; `resolver = "3"` is explicit.
- No re-export, shim or compatibility path. Dated history keeps old paths (SR4 precedent).
- Long runs go through `run.ps1`; no push, no tag; commits end with the Co-Authored-By line from the system reminder.
- Edit files with the Edit tool; check `git diff --cached -M --stat` before committing.

## Review Focus

- A path left behind that no build error catches: `time.rs:87`, `streams_ab.sh`, `test_gate.sh`, `.gitattributes`,
  `corpus.rs:66`. Each has a check in Task 3 or 5.
- Profiles silently ignored: Task 6 times the lib suite (about 3 s, not 30 s).
- `sed` hitting `crates/tatic-kernel/src/` or `tools/runs/src/`: Task 4 uses the anchored pattern and diffs the changed
  line count against the survey.
- `cargo run` / `cargo test` at the root selecting the wrong set: Task 6 runs both.
- `tools/runs` stale exe: Task 6 rebuilds and tests it.

---

### Task 1: Baseline and re-verification

**Files:** none changed (scratch in `.superpowers/rs/`).

- [ ] **Step 1: Save the test list.** `cargo test -j 4 --workspace -- --list 2>/dev/null | grep ': test' | sort >
  .superpowers/rs/sr8-before.txt`. Expected: 749 lines, equal to `.superpowers/rs/before.txt` after sorting.
- [ ] **Step 2: Re-grep the survey counts** and write them to the ledger: `git ls-files src tests benches | wc -l` (94);
  live path-prefixed lines per file with the anchored pattern `(^|[^A-Za-z0-9_/.-])(src|tests|benches)/` over `docs/TOUR.md`,
  `README.md`, `PARKED.md`, `ROADMAP.md`, `docs/learned-vs-fixed.md`, `CLAUDE.md`, `docs/tier-cycle.md`, `scripts/*`,
  `tools/runs/src`. Rule on any count that differs from the spec by more than 10%.
- [ ] **Step 3: Time the lib suite** (`cargo test -j 4 --lib`, warm): about 3 s. Expected to be the profile check's
  reference; record it.
- [ ] **Step 4: Instruction-count baseline.** Build the `church_bv` test exe (`cargo test --no-run --test church_bv`), copy
  it to the scratchpad as `church_bv_sr8_base.exe`, run `icount.ps1 -Cpu 4 -Runs 6 -ExeArgs "--test-threads=1"` on it; record
  best and spread.

### Task 2: The rename commit

**Files:** `src/**`, `tests/**`, `benches/**` → `crates/tatic/...`

- [ ] **Step 1:** `mkdir crates/tatic && git mv src tests benches crates/tatic/`.
- [ ] **Step 2:** `git diff --cached -M --stat | tail -3`. Expected: 94 renames, 0 insertions and 0 deletions.
- [ ] **Step 3: Commit** `tatic: src, tests and benches move to crates/tatic (rename only; the tree does not build until the
  next commit)`.

### Task 3: Manifests

**Files:** create `crates/tatic/Cargo.toml`; modify `Cargo.toml`, `.gitattributes`.

- [ ] **Step 1: Write `crates/tatic/Cargo.toml`** with the root's `[package]` (including `default-run` and its comment),
  `[dependencies]` (`tatic-kernel = { path = "../tatic-kernel" }`), `[dev-dependencies]` (`tatic-rng = { path =
  "../tatic-rng" }`) and both `[[bench]]` tables.
- [ ] **Step 2: Trim the root `Cargo.toml`** to the two profile tables (comments kept) and `[workspace]` with
  `resolver = "3"`, `members = ["crates/tatic", "crates/tatic-kernel", "crates/tatic-rng"]`, `exclude = ["tools/runs"]`, no
  `default-members`.
- [ ] **Step 3: `.gitattributes`:** `tests/golden/*.wat` → `crates/tatic/tests/golden/*.wat`.
- [ ] **Step 4: Verify.** `cargo metadata --locked --format-version 1 >/dev/null` (Expected: succeeds, no lockfile diff, no
  resolver warning); `git ls-files --eol crates/tatic/tests/golden | head -3` shows `eol=lf` attribute matches the index.
- [ ] **Step 5:** `cargo check -j 4 --workspace --all-targets`. Expected: fails only at the three known sites (`corpus.rs`
  ×2, `machine.rs`); anything else is a finding. No commit yet: Tasks 3 and 4 are one commit, so only the rename commit
  (Task 2) is unbuildable.

### Task 4: Code and script paths

**Files:** `crates/tatic/tests/church_bv/{corpus,machine}.rs`, `tools/runs/src/{time,state}.rs`,
`scripts/{streams_ab,test_gate}.sh`.

- [ ] **Step 1: Compile-time paths.** In `corpus.rs`, both `include_str!("../../docs/corpora/…")` become
  `"../../../../docs/corpora/…"`; in `machine.rs` the `#[path]` becomes `"../../../../tools/runs/src/state.rs"`; the
  the `state.rs:3` comment names the new path. Ruling (provisional, user reviews with the plan): `corpus_report` resolves a
  relative `CORPUS` and `CORPUS_RULES` against the repo root (`Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")`), so the
  documented commands in `docs/corpora/hd-own/SOURCE.md:10` and `docs/corpora/souper/SOURCE.md:22` keep working from the
  repo root; an absolute value is unchanged. Grep `std::env::var` of path-valued variables once more (`CHECK_RULES`,
  `LOOP_OUT`, `CREDIT_OUT` use `$RUN_DIR` or absolute paths today) and rule on any other relative one.
  Run `cargo check -j 4 --workspace --all-targets`. Expected: clean apart from the 2 known `church_bv` warnings.
- [ ] **Step 2: Silent paths.** `tools/runs/src/time.rs:87` → `crates\tatic\tests\church_bv\held_11.txt` and its test at
  `:442`; `scripts/streams_ab.sh` lines 5, 22, 23 → `crates/tatic/tests/church_bv`; `scripts/test_gate.sh`: every line containing
  `tests/church_bv` (14, 16, 20, 45, 52, 92, 93 in the survey) mirrors the new layout. Grep afterwards: `git grep -n 'tests/church_bv\|tests\\\\church_bv'
  -- scripts tools` must list only `crates/tatic/…` forms.
- [ ] **Step 3: Run the changed tools' checks.** `scripts/test_gate.sh` takes about 6.5 min (15 to 25 with other jobs), so
  launch it through `run.ps1 -Kind gate -Affinity CFF -Name sr8-test-gate -Detach` with a bounded watcher (Expected: its own
  pass line in `out.log`);
  `cargo test --manifest-path tools/runs/Cargo.toml` (Expected: all pass, including the `held_11` test).
- [ ] **Step 4: Commit** `tatic: manifests and path fixes for crates/tatic` (Tasks 3 and 4 together). The `run.ps1` rows
  in `docs/runs.md` go in their own commit, as in SR4 (2da9517).

### Task 5: Docs

**Files:** `docs/TOUR.md`, `README.md`, `PARKED.md`, `ROADMAP.md`, `docs/learned-vs-fixed.md`, `CLAUDE.md` (substitution
finds 0 lines; only the version-field edit), `docs/corpora/{hd-own,souper}/SOURCE.md` (check; no edit if the code ruling
holds), `docs/tier-cycle.md` (live pointers only), `docs/superpowers/plans/2026-11-04-cleanup-restructure.md` (by hand:
only the SR8 item and the open items; the SR1 to SR7 outcome lines keep their paths). `docs/decisions/*.md`, `docs/runs.md`
and `docs/runs/**` are dated and stay.

- [ ] **Step 1: Substitute** with a boundary-anchored pattern, one file at a time:
  `perl -pi -e 's{(^|[^A-Za-z0-9_/.-])(src|tests|benches)/}{$1crates/tatic/$2/}g'` on the listed live docs (not
  `tier-cycle.md`, `RELATED_WORK.md`, dated plans and specs, `docs/runs/**`). Then `git diff --stat` and compare the changed
  line counts with Task 1's counts. Then restore the lines that must keep old paths: `git show <sha>^:tests/...` recovery
  commands and any prose that says "formerly `src/…`". Expected: `CLAUDE.md` 0 lines changed.
- [ ] **Step 2: `docs/tier-cycle.md`:** list its 50 matching lines first (`grep -nE` with the anchored pattern) and mark each
  by hand: repoint a line only when it names a current file as a pointer ("code:", "see", a cite) outside a dated heading's
  section; a line inside a dated section, a recovery command, or a history sentence keeps its path. Ledger the count
  repointed and kept.
- [ ] **Step 3: `CLAUDE.md`:** version field line names `crates/tatic/Cargo.toml`. `docs/TOUR.md` line 33's crates sentence
  names three crates under `crates/`.
- [ ] **Step 4: Verify.** `bash scripts/tour_check.sh` (Expected: 124 cites, 0 broken) and `bash scripts/cite_check.sh`
  (51 + 124, 0 unresolved). Grep for the old forms: `git grep -nE '(^|[^A-Za-z0-9_/.-])(src|tests|benches)/' -- README.md
  PARKED.md ROADMAP.md CLAUDE.md docs/TOUR.md docs/learned-vs-fixed.md` lists only the intended history lines.
- [ ] **Step 5: Commit** `docs: repoint live cites to crates/tatic`.

### Task 6: Checks, outcome, close

- [ ] **Step 1: Test list.** Same command as Task 1 Step 1; `diff` against `sr8-before.txt`. Expected: identical.
- [ ] **Step 2: Profiles and defaults.** `cargo test -j 4 --lib` warm: about 3 s (Expected: not near 30 s); `cargo run`
  starts the demo (Expected: the demo output; if Cargo refuses to pick among three members, the fallback is `cargo run -p
  tatic` documented at `README.md:107-108`, ruled and ledgered; `default-members` stays absent); `cargo run --bin repl`,
  `cargo test --test church_bv --no-run` and `cargo bench --no-run` resolve at the root; `cargo bench --no-run -j 4` builds both benches; `cargo test --workspace --lib --bins`: all pass.
- [ ] **Step 3: Full suite** through `run.ps1 -Kind probe -Name sr8-suite -Affinity CFF -MaxMemGB 12 -Detach` with a bounded
  watcher; commit the `docs/runs.md` rows separately.
  Expected: green as before the move.
- [ ] **Step 4: Counts.** Build the new `church_bv` exe, copy to the scratchpad, `icount.ps1` with the Task 1 settings.
  Expected: within the A/A spread of the baseline; a larger gap stops the work and goes to the user.
- [ ] **Step 5: Outcome.** Append "Done 2026-11-04 (commits)" to SR8 in the cleanup plan (actual against estimated size,
  the checks, rulings, `Not done`); set this plan and the spec to `status: done`; add `[workspace.package]` hoisting as a
  Next item in the closing report; commit. Then the closing report in the Message format.
