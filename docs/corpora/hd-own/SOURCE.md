# hd-own

- **Source:** written by hand for this repo (2026-10-31), the long forms of 25 routines in the style of Hacker's Delight
  (trailing-bit tricks, averages, min/max by `lt` mask, add/sub/and/or/xor interconversions, bit select, majority). Not a
  copy of the book's text; each line is a short expression.
- **Licence:** same as the repo.
- **Format:** `cases.txt`, `name<TAB>term` per line, `show` syntax over `x`, `y`, `z`; constants 0 and -1 only, so `1` is
  `sub(0, -1)`; `shl1`/`shr1` take a second, ignored operand; `lt` is assumed to give 0 or 1.
- **In scope:** 25 of 25 (no exclusions).
- **Measure:** `CORPUS=docs/corpora/hd-own/cases.txt cargo test --test church_bv --release corpus_report -- --ignored --nocapture`
  (optional `CORPUS_RULES=<mined rules file>`). Expected: 80 operators, the table leaves 54 and changes 17 terms; pinned by
  `corpus::tests::the_hand_written_corpus_reproduces_the_probe_counts`. Findings: `docs/tier-cycle.md`, "Hacker's Delight
  routines".
