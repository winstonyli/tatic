---
status: done
---

# `rewrite.rs` split Implementation Plan (TB3, rewrite half)

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (inline). Steps use checkboxes.

**Goal:** `crates/church-bv/src/rewrite.rs` becomes a parent plus `rewrite/{term,values,plan,rules,rewriter,join,laws,tests}.rs`; no behaviour, item body or test changes.

**Architecture:** top-level items are moved verbatim by a throwaway splitter script that assigns each item to a piece by a table; the parent re-exports every piece with `pub use`; the compiler lists the visibility edits; `job.rs`'s hidden-state test learns the new paths.

**Tech Stack:** Rust 2024 workspace, perl (script run from a file, never stdin), bash, `~/.claude/runs/run.ps1`, `~/.claude/samply/icount.ps1`.

**Spec:** `docs/superpowers/specs/2026-11-04-rewrite-split-design.md`

## Global Constraints

- Moves only: an item body differs from the old one by indentation or by a `pub(super)` visibility keyword (on an item, a field or a method line), nothing else. No renames, no test edits, no signature changes.
- `lib.rs` and every caller outside `rewrite*` stay unchanged (decision d1). All tests move to `rewrite/tests.rs` (e1).
- Commits end with the Co-Authored-By line; long runs through `run.ps1`; Edit tool for hand edits; `git diff --stat` before committing. No push, tag or bump.
- The scratchpad holds the splitter and the baseline files; python is not used.

## Review Focus
- `Node` ambiguous between the kernel glob and the local enum (Task 2 step 2 adds `pub use term::Node;`; the first compile shows it if not).

- A `thread_local!` or `static` split from its accessor fn, or a `thread_local!` block cut in two (Task 2 keeps each statement whole; Task 5 reference sweep and the lib suite exercise them).
- A test that silently stops running (Task 2 step 4 compares the test list).
- A hidden-state entry that stops matching (Task 3 breaks one on purpose and expects FAIL).
- An item changed beyond visibility (Task 2 step 3 multiset diff).
- A doc cite to `rewrite.rs#symbol` left pointing at the parent (Task 4, `tour_check`).

---

### Task 1: Baseline and map

- [ ] **Step 1:** `cargo test -j 4 --workspace -- --list 2>/dev/null | grep ': test' | sort > .superpowers/rs/tb3-before.txt` (expected 757 on 2026-11-04 at e7c8427).
- [ ] **Step 2:** save the old file: `cp crates/church-bv/src/rewrite.rs <scratchpad>/rewrite_old.rs`; list its top-level items with start lines (a top-level item starts at a column-0 line that is not `}`/`)`/blank and whose preceding lines are its doc comments and attributes). Ledger the table.
- [ ] **Step 3:** write the assignment table (item start line -> piece) from the spec's table; every item, test and helper gets exactly one piece; a `#[test]` item and the items only tests use (`join_trace`, `PIN_SOURCE`, test helper fns/consts) go to `tests`; the stale header comment above line 3703 ("Searching for the carry-state encoding") goes with `tests` unchanged. Ruling for any item that sits on a boundary: with its only caller, else with the concern that owns its data. Ledger the table. A `thread_local!` block, an `impl` block and a `static` stay whole.

### Task 2: Split (the compiler is the test)

- [ ] **Step 1: RED check.** Create `rewrite/` with a parent that declares the eight `mod`s and `pub use` the seven non-test pieces, and empty piece files; `cargo check` fails on missing items. (This is the state the move starts from.)
- [ ] **Step 2: Move.** Write `<scratchpad>/split.pl` (run as `perl split.pl`, reading `rewrite_old.rs` and the table): it writes each piece as `use super::*;` plus the items assigned to it, verbatim and in their old order, and the parent as the old file's two `use` lines (`use super::*;` stays), the `mod`/`pub use` lines, one explicit `pub use term::Node;` (the kernel's `Node` and this one are both glob-imported at the crate root; without it every piece but `term` fails with E0659) and nothing else. `tests.rs` is `use super::*;` plus its items; `#[test]` attributes and their order are kept.
- [ ] **Step 3: Compile and fix visibility.** `cargo check -j 4 -p church-bv --all-targets`; for each "private" error add `pub(super)` where the item, field or method is declared (nothing else); for a `private_interfaces` warning make the `pub` function `pub(super)` too. Repeat until clean apart from the 2 known warnings. Ledger the count of items touched. Then the byte check: for old and new, take every file's lines, trim, drop blanks, drop `use super::*;`, `mod x;`, `pub use x::*;`, delete every `pub(super) `, sort; `diff` the two sorted lists. Expected: only the added `pub use term::Node;` line.
- [ ] **Step 4:** test list equals `tb3-before.txt` after mapping `rewrite::` to `rewrite::tests::` for the 51 moved names (`diff` expected empty). The lib suite waits for Task 3 (the hidden-state test still names `rewrite.rs`); do not commit before it. Task 2 and Task 3 are one commit, `church-bv: split rewrite.rs into rewrite/ pieces`.

### Task 3: Hidden state

- [ ] **Step 1:** read `hidden_state_is_classified` in `job.rs`: it walks `src/*.rs` by `read_dir` (not `src/uniform/`). Make the walk also read `src/rewrite/*.rs` and name each such file `rewrite/<file>` in the lists (they key on `file_name`; use the path relative to `src` with `/` as separator). `JobSwap` and `JobAlias` compare `file == "job.rs"` and are unaffected.
- [ ] **Step 2:** change the five entries to the new files (`OP_CACHE`, `TABLE` in `rewrite/term.rs`; `CLOSED` in `rewrite/plan.rs` with its fn; `COUNTING` in `rewrite/plan.rs`; `CACHE` in `rewrite/rules.rs`; confirm each by grep, not from this plan).
- [ ] **Step 3 (can fail):** rename one entry's file in the list, run `cargo test -p church-bv --lib hidden_state_is_classified` — Expected: FAIL naming that static; revert the rename; run again — Expected: PASS. Then `cargo test -j 4 -p church-bv --lib` passes with 318 tests, and the one commit of Tasks 2 and 3 is made.

### Task 4: Docs

- [ ] **Step 1:** `docs/TOUR.md`: add the `rewrite/` pieces (one line each) to the church-bv module list; repoint every `rewrite.rs#symbol` cite to the file that now holds the symbol (`grep -n 'rewrite.rs' docs/TOUR.md`; the symbol's file from the table); `PARKED.md` and code comments (`uniform/bitwise.rs`, `uniform/width.rs`, `wasm.rs`, any `rewrite.rs#`) the same where they name a symbol; add a PARKED entry for the `encoding.rs` half (what: the five-file split sketched in the spec's survey; why parked: decision c1; trigger: this split landed; status: parked). `bash scripts/tour_check.sh` and `bash scripts/cite_check.sh` pass.
- [ ] **Step 2:** commit `docs: rewrite/ pieces`.

### Task 5: Checks and close

- [ ] **Step 1:** full suite through `run.ps1 -Kind probe -Name tb3-suite -Affinity CFF -MaxMemGB 12 -Detach` (expected 709 passed, 0 failed: the TB1 step 2 suite had 708, plus the once-only re-entry test); `test_gate.sh` through `run.ps1 -Kind gate -Name tb3-test-gate` (0 failed).
- [ ] **Step 2:** build the bin with `--profile test`, run the reference sweep (`ref_sweep2.sh`) and diff `WORK`, result files and the tsv minus its seconds column against `ref1` (expected identical); `icount.ps1 -Cpu 4 -Runs 3` old bin against new on it: expected equal within the A/A spread.
- [ ] **Step 3:** one Sonnet whole-branch review with the Review Focus; one fix pass. Append the outcome to the TB3 item, set spec and plan `status: done`, closing report.
