#!/bin/bash
# open_laws.sh <exe>: phase 2's stream probe. Per seed (`table`: 20000 of the class table's representatives; else a family's
# pool; `SEEDS` how many; `PAIR=grown` pairs grown terms only; `FRONTIERS=1` grows only terms the table does not store; `OPSETS` comma-separated operator sets the table seed is restricted to, `all` none, `;` joining sets that run as separate streams with their functions counted together (MIX); `LEVELS` growths, default 3) and growth budget (`BUDGETS`, terms per level, default 20000), laws the class table leaves open by growth level
# and size, open ones refuted at width 8 counted as false, from the throwaway probe `search::open_law_counts` (reverted;
# the exe needs `docs/runs/2026-10-23/patches/open_law_counts_table.patch`).
EXE=$1
for o in ${OPSETS:-all}; do
for fr in ${FRONTIERS:-0}; do
for s in ${SEEDS:-20000}; do
for g in ${BUDGETS:-20000}; do
  for f in ${FAMS:-table add3 sbo3 mix3 cmp3d}; do
    echo "OPS $o FRONTIER $fr SEEDS $s BUDGET $g $f"
    OL_OPS=$o OL_FRONTIER=$fr OL_PAIR=${PAIR:-seed} OL_SEEDS=$s OL_GEN=$g OL_FAMILY=$f OL_SALT=1 OL_PER=${PER:-300} OL_LEVELS=${LEVELS:-3} "$EXE" search::open_law_counts --exact --ignored --nocapture < /dev/null 2>&1 | grep -E "^(TERMS|OPEN|WHY|FUNCS|OPSETS|EXAMPLE|MIX)|panic"
  done
done
done
done
done
