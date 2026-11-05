---
status: draft
---

# Split `docs/tier-cycle.md` by section (DOC2)

Item DOC2 of `docs/superpowers/plans/2026-11-04-cleanup-restructure.md`; decision D3 (split by H2) and f1 below. Facts are from a
read-only look on 2026-11-04 (commit 291cb59). DOC3 (the one cite checker) is done and is a prerequisite.

## Intent

`docs/tier-cycle.md` is 8558 lines: 18 H2 sections, two of them giants ("Speed: the miner, the sweep and the join" 2550 lines,
"The kernel" 2236). It is the findings log that code comments, `PARKED.md` and `TOUR.md` cite by section title. After the split each
section is a file under `docs/tier-cycle/`, the two giants are split again at their H3s, a checked index lists every file, and every
live cite still resolves. Nothing in any section changes.

## Decided by the user (2026-11-04)

- D3: split by H2. f1: a directory of H2 files plus an index (`README.md`), H3 splits for the two giants.

## Design

**Layout.** `docs/tier-cycle/README.md` is the index. An ordinary H2 is `docs/tier-cycle/<nn>-<slug>.md` (`nn` = its position, two
digits, so a sorted listing is the document order; `slug` = the lowercase heading, non-alphanumerics to `-`). The preamble before the
first H2 (the H1 title and its lead lines, lines 1-6) is `00-title.md`. A giant H2 is a directory `<nn>-<slug>/`: `00-intro.md`
holds the H2 line and any text before its first H3, and each H3 is `<mm>-<slug>.md`. Heading levels are not changed (a file may begin
with `###`); no heading is renamed. The file is the unit of text, so concatenating all files in index order reproduces the old file
byte for byte.

**Index.** `README.md` states what the log is (the old H1 and first lead lines stay in `00-title.md`; the index does not copy them),
then one line per file: relative link, the heading's title and the file's line count. It is generated once by the plan's script and
checked by `scripts/tier_cycle_check.sh` (a new, small script): every file under `docs/tier-cycle/` except `README.md` is linked from
the index, every link resolves, the files' concatenation order equals the index order, and no file is empty.

**Cites.** A section cite is today ``docs/tier-cycle.md, "Title"`` (also `docs/tier-cycle.md "Title"` and `section "Title"`). The cite
form becomes ``docs/tier-cycle/, "Title"``: a path-prefix replacement of `docs/tier-cycle.md` by `docs/tier-cycle/` in live docs,
code comments and scripts (about 42 non-history files, `RELATED_WORK.md` among them, plus `README.md`, `CLAUDE.md`, `PARKED.md`, `ROADMAP.md`, `TOUR.md`).
`scripts/cite_check.pl` takes the directory as its target: anchors come from every `docs/tier-cycle/**/*.md` line (same heading and
emphasis stripping), the regex accepts the new prefix, and `scripts/cite_check_check.sh` gets the new form. The section titles are
unchanged, so every cite that resolves today resolves after.
`RELATED_WORK.md` is a live doc that `cite_check` reads, so its cites to the log are rewritten too (its cites to itself are unchanged).
History is left as it is: `docs/runs/**` (including the `.patch` files, which must keep applying), dated plans and specs under
`docs/superpowers/` keep the old name; a reader follows it with `git show 291cb59:docs/tier-cycle.md`.
The new spec, plan and the cleanup plan state that once.

**Relative links.** The log has 6 links; the one relative link (`](learned-vs-fixed.md)`, in "Learned and fixed parts") becomes
`](../learned-vs-fixed.md)` in whichever file holds it (one deliberate edit); the others are absolute URLs. Other docs that link into
the log by file name (none expected; the plan greps) are repointed.

## Non-goals

Editing, trimming or reordering any section; renaming a heading; splitting a section other than the two giants; a table of contents
beyond the index; splitting `RELATED_WORK.md` (DOC1).

## Anti-goals

A cite that resolves today and not after; a byte of section text changed or lost (the concatenation check); a stale `tier-cycle.md`
left behind (the old file is deleted in the same commit, no stub); an index that drifts from the directory (the check script).

## Verification

Before: record `cite_check.sh` output (`N section cites checked, 0 unresolved`) and the SHA-256 of the old file. After: the same count
and 0 unresolved; the concatenation of the files in index order (excluding `README.md`) has the old file's SHA-256 except for the
one link edit (diff shows exactly that line); `scripts/tier_cycle_check.sh` passes; `bash scripts/tour_check.sh` passes; `git grep -n
'tier-cycle\.md'` outside the history set above returns nothing.

## Left to the builder

The slug text; the index's wording; whether a tiny H3 file (under about 15 lines) stays in its neighbour (no: one file per H3).
