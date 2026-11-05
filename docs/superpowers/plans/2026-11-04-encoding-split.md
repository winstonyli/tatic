---
status: draft
---

# `encoding.rs` split Implementation Plan (TB3, encoding half)

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (inline). Steps use checkboxes.

**Goal:** `crates/church-bv/src/encoding.rs` becomes a parent plus `encoding/{gates,good,division,proofs,tables,tests}.rs`; no behaviour, item body or test changes.

**Architecture:** top-level items move verbatim by a throwaway splitter (the `rewrite` split's `chunks.pl` and `split.pl` in the previous session's scratchpad are the model; rewrite them for this file's table); the parent re-exports every piece with `pub use`; the compiler lists the visibility edits; `job.rs`'s hidden-state test learns the new paths.

**Tech Stack:** Rust 2024 workspace, perl (script run from a file, never stdin; no python), bash, `~/.claude/runs/run.ps1`.

**Spec:** `docs/superpowers/specs/2026-11-04-encoding-split-design.md`

## Global Constraints

- Moves only: an item body differs by indentation or a `pub(super)` keyword on an item, field or method line. No renames, no test edits, no signature changes.
- `lib.rs` and every caller outside `encoding*` stay unchanged. All tests go to `encoding/tests.rs`.
- Commits end with the Co-Authored-By line; long runs through `run.ps1` (`-MaxMemGB 12 -Affinity CFF`); Edit tool for hand edits; `git diff --stat` before committing. No push, tag or bump.
- Perl pitfall from the `rewrite` split: write `"pub use ${_}::*;\n"`, not `$_::`.

## Review Focus

- A `thread_local!` (`CONSTANTS` inside `constant`, `BODIES` inside `tab_bdd`/`table_expr`) cut from its fn: keep each statement whole (Task 2); the lib suite and the reference sweep exercise them.
- A test that silently stops running, in particular the 7 `#[ignore]`d ones: Task 2 step 4 compares the full `--list` including ignored.
- A hidden-state entry that stops matching: Task 3 breaks one on purpose and expects FAIL.
- An item changed beyond visibility: Task 2 step 3 multiset diff.
- A script or doc naming an `encoding::<test>` path that now needs `tests::`: Task 4 greps.

---

### Task 1: Baseline and map

- [ ] **Step 1:** `cargo test -j 4 -p church-bv --lib -- --list 2>/dev/null | grep ': test$' | sort > .superpowers/rs/tb3b-before.txt`; record the count and the `encoding::` subset (26).
- [ ] **Step 2:** copy the file to the scratchpad (`encoding_old.rs`); write `chunks.pl` (a chunk = its leading `///`/`//`/`#[` lines plus a head line starting an item; `thread_local!` blocks stay whole inside their fn) and print `start end kind test? name` for every top-level chunk.
- [ ] **Step 3:** write the assignment (chunk name -> piece) from the spec's table; every chunk gets exactly one piece; a chunk with `#[test]`, or only used by tests and `#[cfg(test)]`-gated, goes to `tests`. For each pub item check its callers with `grep -rn '\bname\b' crates/church-bv/src` and apply the spec's rule where the table's piece is not the only owner; ledger each ruling. Expected: a total with no chunk unassigned (assert in the script).

### Task 2: Split (the compiler is the test)

- [ ] **Step 1: Split.** `split.pl <old> <tsv> <outdir>` writes each piece as `use super::*;` plus its chunks verbatim in their old order, and the parent as the old file's first lines (its `use`s), `mod gates; mod good; mod division; mod proofs; mod tables; #[cfg(test)] mod tests;` and `pub use <piece>::*;` for the five non-test pieces. Copy the output over `crates/church-bv/src/` (create `encoding/`).
- [ ] **Step 2: Compile and fix visibility.** `cargo check -j 4 -p church-bv --all-targets --message-format json` and add `pub(super)` where errors say (the pass: parse JSON, add the keyword at each reported definition line; for "field/method is private" errors without a definition span, add it by name in the right struct or impl). Repeat until clean. A `pub fn` mentioning a `pub(super)` type becomes `pub(super)`. Expected: no errors; warnings only the two known ones in `uniform/`.
- [ ] **Step 3:** multiset check: `sed 's/pub(super) //' | sort` of the old file against the same over the new files plus the parent; `diff` shows only added lines (`mod`, `pub use`, `use super::*;`, blanks). Expected: no `<` lines.
- [ ] **Step 4:** test list equals the baseline after mapping `encoding::tests::` to `encoding::` (ignored ones included): `comm -3` empty.

### Task 3: Hidden state

- [ ] **Step 1:** in `job.rs`, change the two `encoding.rs` entries to their new files (grep for where `CONSTANTS` and `BODIES` now live) and make the directory walk cover `src/encoding/` the way it covers `src/rewrite/`.
- [ ] **Step 2 (can fail):** misfile one entry, run `cargo test -p church-bv --lib hidden_state_is_classified` - Expected: FAIL naming that static; restore; run again - Expected: PASS.
- [ ] **Step 3:** `cargo test -j 4 -p church-bv --lib` - Expected: 318 passed, 0 failed (the same count). Commit Tasks 2 and 3 together: `church-bv: split encoding.rs into encoding/ pieces`.

### Task 4: Docs

- [ ] **Step 1:** `docs/TOUR.md`: repoint the 3 `encoding.rs#symbol` cites to their piece, rewrite its module line with the piece list. `git grep -n 'encoding\.rs\|encoding::' -- ':!docs/runs' ':!docs/superpowers' ':!docs/tier-cycle.md' ':!RELATED_WORK.md'` and fix every live mention (PARKED.md symbol mentions, scripts naming `encoding::<test>`). Delete the `encoding.rs` entry from `PARKED.md`. Expected: `bash scripts/tour_check.sh` and `bash scripts/cite_check.sh` pass.
- [ ] **Step 2:** commit `docs: encoding/ pieces`.

### Task 5: Checks and close

- [ ] **Step 1:** `run.ps1 -Kind probe -Name tb3b-suite -Affinity CFF -MaxMemGB 12 -Detach -Command "cargo test -j 4 --workspace"` - Expected: 709 passed, 0 failed (watcher on `run.json`); then `run.ps1 -Kind gate -Name tb3b-test-gate -Command "bash scripts/test_gate.sh"` - Expected: 0 failed.
- [ ] **Step 2:** build the bin (`cargo build -j 4 --profile test -p church-bv --bin church-bv`), run the reference sweep (`ref_sweep2.sh <out> <exe> sweep`; old exe is the pre-split bin saved before Task 2) and compare `WORK`, the result files and `cold_streams.tsv` minus column 7 - Expected: identical.
- [ ] **Step 3:** one Sonnet whole-branch review with the Review Focus; one fix pass. Append the outcome to the TB3 item of the cleanup plan, set spec and plan `status: done`, closing report.
