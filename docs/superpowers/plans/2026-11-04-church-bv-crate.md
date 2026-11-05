---
status: active
---

# `church_bv` as a workspace crate, step 1 (TB1)

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (inline, as SR4 and SR8). Steps use checkboxes.

**Goal:** `crates/tatic/tests/church_bv/` becomes the lib crate `crates/church-bv`; the 749-name test list, test results and
exe name are unchanged. Step 2 (the bin) is not in this plan.

**Architecture:** a rename-only commit, then manifest and path fixes in one commit, then docs, then checks.

**Spec:** `docs/superpowers/specs/2026-11-04-church-bv-crate-design.md`

## Global Constraints

- Test list stays the 749 names of `.superpowers/rs/sr8-before.txt`; package `tatic` and its other tests, benches and bins
  are untouched; profiles stay in the root manifest.
- No shim or re-export; dated history keeps old paths. No push, tag or bump. Commits end with the Co-Authored-By line.
- Long runs through `~/.claude/runs/run.ps1`; edit files with the Edit tool; `git diff --cached -M --stat` before committing.

## Review Focus

- A data file read from the old place, silently: `class_key.txt` (`classes.rs:17,563`), `held_*.txt` (`classes.rs:612`,
  `job.rs:696`, `time.rs:87`, two scripts). Task 3 greps every form and Task 5 runs the gate script.
- A relative path that resolves against the changed cwd: `corpus_report` (`from_repo_root`, unchanged) and any `CARGO_MANIFEST_DIR` join.
- Dead-code warnings the lib now emits: Task 1 counts, Task 3 settles.
- `tatic` losing a dev-dependency another file uses (`tatic-rng`): Task 3 checks `cargo check --workspace --all-targets`.
- Lockfile: only the new package may appear (Task 3).

---

### Task 1: Baseline

- [ ] **Step 1:** `git ls-files crates/tatic/tests/church_bv | wc -l` (expected 28, the data files and `uniform/` included);
  `cargo test -j 4 --workspace -- --list 2>/dev/null | grep ': test' | sort` equals `sr8-before.txt` (749).
- [ ] **Step 2:** re-grep the live path counts the spec lists, per file: `git grep -cE 'church_bv' -- <file>` for README, PARKED,
  ROADMAP, `docs/TOUR.md`, `docs/learned-vs-fixed.md`, `docs/tier-cycle.md`, `scripts`, `tools/runs/src`, `crates/tatic/src`;
  rule on any count more than 10% off.
- [ ] **Step 3:** save the old exe as `church_bv_tb1_base.exe` in the scratchpad (path from `cargo test --no-run --test church_bv`
  output) and run `icount.ps1 -Cpu 4 -Runs 6 -ExeArgs "--test-threads=1"`; record best and spread (SR8's was 427.3 to 428.1 G).
- [ ] **Step 4:** count `git grep -n "include_str\|CARGO_MANIFEST_DIR\|#\[path" crates/tatic/tests/church_bv`: the list is Task 3's work list.

### Task 2: The rename commit

- [ ] **Step 1:** `mkdir -p crates/church-bv/src crates/church-bv/data`; `git mv crates/tatic/tests/church_bv/{class_key,held_*}.txt crates/church-bv/data/`
  (the glob expanded in the shell); `git mv crates/tatic/tests/church_bv/main.rs crates/church-bv/src/lib.rs`; `git mv` the rest
  (`*.rs` and `uniform/`) to `crates/church-bv/src/`.
- [ ] **Step 2:** `git diff --cached -M --stat | tail -2`: all renames, 0 insertions and 0 deletions; `ls crates/tatic/tests` has no `church_bv`.
- [ ] **Step 3: Commit** `church-bv: tests/church_bv moves to crates/church-bv (rename only; the tree does not build until the next commit)`.

### Task 3: Manifest and path fixes

**Files:** create `crates/church-bv/Cargo.toml`; modify root `Cargo.toml`, `lib.rs`, `classes.rs`, `corpus.rs`, `job.rs`,
`machine.rs`, `tools/runs/src/{time,state}.rs`, `scripts/{streams_ab,test_gate}.sh`, `crates/tatic/src/lib.rs`.

- [ ] **Step 1: Manifest.** `crates/church-bv/Cargo.toml`: `[package] name = "church-bv"`, `version/edition/license.workspace = true`,
  `[dependencies] tatic-kernel.workspace, tatic-rng.workspace, hashbrown.workspace, mimalloc.workspace` (all four are
  `[workspace.dependencies]` entries). Root `members` gains `"crates/church-bv"`; the members comment names four crates.
- [ ] **Step 2: Allocator.** In `lib.rs` the `#[global_allocator]` becomes `#[cfg(test)]` and its comment says the shipping one lives
  in the bin (step 2). Repoint the comment in `crates/tatic/src/lib.rs` (lines 12-13) so it no longer lists `tests/church_bv/main.rs`.
- [ ] **Step 3: Compile-time and runtime paths.** `corpus.rs` two `include_str!` to `../../../docs/corpora/...`; `machine.rs`
  `#[path]` to `../../../tools/runs/src/state.rs`; `classes.rs:17` to `../data/class_key.txt`; `classes.rs:563,612` `CARGO_MANIFEST_DIR` joins to
  `data/...`; `job.rs:696` lists the `.rs` sources (a text-scan test), so its join becomes `src`. `tools/runs/src/state.rs:3` comment.
- [ ] **Step 4: Silent paths.** `time.rs:87` to `crates\church-bv\data\held_11.txt` and its test `:442`; `streams_ab.sh` lines
  5, 22, 23 and `test_gate.sh` lines 14, 16, 20, 45, 52, 92, 93 to `crates/church-bv/data` (the fixture root mirrors the layout).
  Afterwards `git grep -nE 'tests/church_bv|tests\\\\church_bv' -- scripts tools crates` lists nothing.
- [ ] **Step 5: Verify.** `cargo check -j 4 --workspace --all-targets`: record the warning count from the lib's non-test build.
  If it is over a handful, add one crate-level `#![cfg_attr(not(test), allow(dead_code))]` to `lib.rs` with a comment saying step 2
  deletes it, and recheck: clean apart from the 2 known `church_bv` warnings. `cargo metadata --locked` fails only because
  `Cargo.lock` needs the new package: run `cargo metadata --format-version 1 >/dev/null`, then `git diff Cargo.lock` shows one
  new `[[package]] church-bv` block and nothing else.
- [ ] **Step 6:** `cargo test --manifest-path tools/runs/Cargo.toml` (45 pass) and rebuild `tools/runs` release (`runs.exe` embeds
  nothing path-wise but is rebuilt for the `time.rs` change). Launch `scripts/test_gate.sh` through `run.ps1 -Kind gate -Affinity CFF
  -Name tb1-test-gate -Detach` with a bounded watcher; expected 0 failed.
- [ ] **Step 7: Commit** `church-bv: manifest and path fixes for crates/church-bv` (the `docs/runs.md` rows go in their own commit).

### Task 4: Docs

- [ ] **Step 1:** repoint live cites with the anchored pattern `crates/tatic/tests/church_bv/` to `crates/church-bv/src/` in
  `README.md`, `PARKED.md`, `ROADMAP.md`, `docs/TOUR.md`, `docs/learned-vs-fixed.md`; data-file names (`held_*.txt`, `class_key.txt`)
  to `crates/church-bv/data/`. `docs/tier-cycle.md`: only lines that exist under the new path and are outside dated sections and
  `git show` recovery commands (SR8's rule); ledger repointed and kept counts.
- [ ] **Step 2:** commands: `cargo test ... --test church_bv` to `cargo test ... -p church-bv --lib` (README lines 111 and 137, the doc comments at `driver.rs:624` and
  `machine.rs:330`, `docs/corpora/{hd-own,souper}/SOURCE.md`, `docs/TOUR.md` line 3, `Cargo.toml` profile comments;
  grep `test church_bv` repo-wide outside dated plans, specs and `docs/runs`). README line 77 "`<church_bv test exe>`" stays true.
- [ ] **Step 3:** `docs/TOUR.md`: line 3 and line 38 ("`main.rs` holds only the `mod` lines and the allocator" becomes `lib.rs`),
  and a line saying `church-bv` is the fourth crate; `CLAUDE.md` needs no edit (check by grep). `bash scripts/tour_check.sh` and
  `bash scripts/cite_check.sh` pass.
- [ ] **Step 4: Commit** `docs: repoint live cites to crates/church-bv`.

### Task 5: Checks and close

- [ ] **Step 1:** test list equals `sr8-before.txt`; `cargo test -j 4 --workspace --lib --bins` passes; `cargo test -p church-bv --lib --no-run`
  resolves; `cargo run` and `cargo bench --no-run -j 4` still resolve at the root.
- [ ] **Step 2:** full suite through `run.ps1 -Kind probe -Name tb1-suite -Affinity CFF -MaxMemGB 12 -Detach` with a bounded
  watcher: 701 passed as SR8's; `docs/runs.md` rows in their own commit.
- [ ] **Step 3:** build the new exe, copy to the scratchpad, `icount.ps1` with Task 1's settings: within the A/A spread; a larger
  gap stops the work and goes to the user.
- [ ] **Step 4:** whole-branch review by one Sonnet agent with the Review Focus above. Fix findings in one pass.
- [ ] **Step 5:** append "Done 2026-11-04 (commits)" to TB1 in the cleanup plan (actual against estimate, checks, rulings, `Not done:
  step 2`), set this plan and the spec `status: done`, add step 2 to `ROADMAP.md`/`PARKED.md` as its own item, commit, closing report.
