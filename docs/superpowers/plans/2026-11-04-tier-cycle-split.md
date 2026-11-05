---
status: active
---

# `tier-cycle.md` split Implementation Plan (DOC2)

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (inline). Steps use checkboxes.

**Goal:** `docs/tier-cycle.md` becomes `docs/tier-cycle/` (title, one file per H2, the two giants split at H3, an index), with every live cite rewritten and the cite checker reading the directory.

**Architecture:** a throwaway perl splitter cuts the file at heading lines into numbered files; a second script writes the index; `cite_check.pl` and its check learn the directory; a prefix replacement rewrites live cites; the old file is deleted.

**Tech Stack:** bash, perl (run from files, never stdin; no python), git.

**Spec:** `docs/superpowers/specs/2026-11-04-tier-cycle-split-design.md`

## Global Constraints

- Section text is moved verbatim; the only content edit is the one relative link (`](learned-vs-fixed.md)` to `](../learned-vs-fixed.md)`).
- Do not touch `docs/runs/**`, dated plans and specs under `docs/superpowers/` (except the three documents of this item). `RELATED_WORK.md` is live: its cites to the log are rewritten.
- Commits end with the Co-Authored-By line; Edit tool for hand edits; `git diff --stat` before committing; line endings as the repo's (LF in working tree, check `git diff --stat` for whole-file noise). No push, tag or bump.

## Review Focus

- A cite that resolved before and does not after (Task 4 compares counts and runs the checker; `bash scripts/cite_check.sh`).
- A heading line inside a fenced code block mistaken for a section (Task 1 splits only on `## ` / `### ` lines outside fences; the concatenation check would still pass, so Task 1 also lists the cut lines for a look).
- A cite whose title is a bold lead-in or list item, not a heading (the checker matches any line start; Task 3 keeps that).
- A cite form not caught by the prefix replacement, e.g. ``docs/tier-cycle.md`` followed by a line break and the title, or "tier-cycle.md" without `docs/` (Task 4 greps the leftovers).
- A relative link that breaks (Task 2 step 3).

---

### Task 1: Baseline and cut points

- [ ] **Step 1:** record `bash scripts/cite_check.sh | tail -2` (the count of cites, 0 unresolved), `sha256sum docs/tier-cycle.md`, and `git grep -n 'tier-cycle\.md' | wc -l`; save to `.superpowers/rs/doc2-before.txt`.
- [ ] **Step 2:** write `cuts.pl` (scratchpad) that lists, for the old file, each `^## ` line and, inside "Speed: ..." and "The kernel", each `^### ` line, skipping lines inside ``` fences, as `line<TAB>level<TAB>title`. Look at the list: 18 H2 and 3 + 10 H3 expected (the survey saw H3 at 3080, 3679, 4110 under Speed and ten under The kernel).

### Task 2: Split

- [ ] **Step 1:** write `split.pl`: preamble (lines before the first `## `) to `docs/tier-cycle/00-title.md`; each H2 to `<nn>-<slug>.md` (nn from 01); for Speed and The kernel a directory `<nn>-<slug>/` with `00-intro.md` (up to the first `###`) and `<mm>-<slug>.md` per H3 (mm from 01). Run it into a scratch dir first.
- [ ] **Step 2:** concatenation check: concatenating the files in sorted path order (title, then each H2 in order; a directory's files in order) equals the old file - Expected: identical `sha256sum`.
- [ ] **Step 3:** apply the link edit to the file holding `](learned-vs-fixed.md)`, then re-diff - Expected: exactly that one line differs. `git grep -n '](' docs/tier-cycle/` shows no other relative link.
- [ ] **Step 4:** write `docs/tier-cycle/README.md` (what the log is and how to cite it in one paragraph, then one line per file: link, title, line count, in document order) from a script, not by hand.

### Task 3: Check scripts

- [ ] **Step 1: RED.** Write `scripts/tier_cycle_check.sh` (every non-README file linked from the index, every link resolves, link order equals sorted file order, no empty file; exit 1 with the offending names) and run it before writing the README: Expected: FAIL naming a missing index. Then with the README: Expected: PASS. Break it on purpose (delete one index line): Expected: FAIL naming that file; restore.
- [ ] **Step 2:** `scripts/cite_check.pl`: `@targets` reads `docs/tier-cycle/**/*.md` for the anchors of the key `docs/tier-cycle/` (find via `File::Find`); the cite regex alternation includes `docs/tier-cycle/` (the prefix then a comma, space or backtick as today); the default doc list drops `docs/tier-cycle.md` (the cites in the log itself are checked through the directory, which holds the section files). Update `scripts/cite_check_check.sh` cases to the new form and run it - Expected: its cases pass.

### Task 4: Rewrite cites, delete the old file

- [ ] **Step 1:** replace `docs/tier-cycle.md` by `docs/tier-cycle/` in the live set: `git grep -l 'tier-cycle\.md' -- ':!docs/runs' ':!docs/superpowers'` plus the three documents of this item and the cleanup plan only where it states live paths (DOC2 item); `sed -i` per file, `git diff --stat` for sanity.
- [ ] **Step 2:** `git rm docs/tier-cycle.md`. Grep leftovers: `git grep -n 'tier-cycle\.md' -- ':!docs/runs' ':!docs/superpowers'` - Expected: none; also `git grep -n 'tier-cycle[^/.a-z-]'` for bare mentions in live docs and fix by hand.
- [ ] **Step 3:** `bash scripts/cite_check.sh` - Expected: the same cite count as the baseline, 0 unresolved; `bash scripts/tier_cycle_check.sh`; `bash scripts/tour_check.sh`; `bash scripts/cite_check_check.sh`. `cargo check -j 4 --workspace` (comments only changed - Expected: clean).
- [ ] **Step 4:** commit `docs: split tier-cycle.md into docs/tier-cycle/`.

### Task 5: Close

- [ ] **Step 1:** one Sonnet review of the diff with the Review Focus (read-only); one fix pass.
- [ ] **Step 2:** append the outcome to the DOC2 item (cite count, file count, `git show 291cb59:docs/tier-cycle.md` for the old name); `ROADMAP.md`/`CLAUDE.md` mentions already rewritten in Task 4; set spec and plan `status: done`; closing report.
