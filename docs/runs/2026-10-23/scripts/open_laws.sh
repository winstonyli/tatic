#!/bin/bash
# open_laws.sh <exe>: phase 2's stream probe. Per family, laws the class table leaves open by growth level and size, from
# the throwaway probe `search::open_law_counts` (reverted; the exe needs `docs/runs/2026-10-23/patches/open_law_counts.patch`).
EXE=$1
for f in add3 sbo3 mix3 cmp3d; do
  OL_FAMILY=$f OL_SALT=1 OL_PER=300 OL_LEVELS=3 "$EXE" search::open_law_counts --exact --ignored --nocapture < /dev/null 2>&1 | grep -E "^(TERMS|OPEN)|panic"
done
