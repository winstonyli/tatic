#!/bin/bash
# open_laws.sh <exe>: phase 2's stream probe. Per seed (`table`: 20000 of the class table's representatives; else a family's
# pool) and growth budget (`BUDGETS`, terms per level, default 20000), laws the class table leaves open by growth level
# and size, open ones refuted at width 8 counted as false, from the throwaway probe `search::open_law_counts` (reverted;
# the exe needs `docs/runs/2026-10-23/patches/open_law_counts_table.patch`).
EXE=$1
for g in ${BUDGETS:-20000}; do
  for f in ${FAMS:-table add3 sbo3 mix3 cmp3d}; do
    echo "BUDGET $g $f"
    OL_GEN=$g OL_FAMILY=$f OL_SALT=1 OL_PER=300 OL_LEVELS=3 "$EXE" search::open_law_counts --exact --ignored --nocapture < /dev/null 2>&1 | grep -E "^(TERMS|OPEN)|panic"
  done
done
