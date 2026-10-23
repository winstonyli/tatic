#!/bin/bash
# join_budget.sh <exe>: how does the visit budget a held-out law needs grow with its size? Per family, the salt-1 ref
# library (run 2026-10-22-gen-warm-fix, mon_1) serves each of the size-band's held-out sets (run 2026-10-22-size-band,
# salt 11; sizes 7, 9, 11, and 13 for cmp3d) separately at each JOIN_VISIT in VISITS (default "250 500 1000 2000 5000
# 20000"). Prints per serve: free laws (no whole-term machine proof), not proved, joined, searches, terms reached, wall ms.
EXE=$1; T="${RUN_DIR:-$TEMP}/join_budget"; R="$LOCALAPPDATA/claude-runs/tatic/2026-10-22"
mkdir -p "$T"
serve() { # fam rules laws visit tag
  local t0=$(date +%s%N)
  JOIN_VISIT=$4 RULEMINER_FAMILY=$1 CHECK_FAMILY=$1 RULEMINER_DEEP3=1 MACHINE_BANNER=0 CHECK_RULES="$(cygpath -w "$2")" CHECK_LAWFILE="$(cygpath -w "$3")" \
    "$EXE" search::rule_set_kernel_check --exact --ignored --nocapture < /dev/null > "$T/$5.log" 2>&1
  local ms=$(( ($(date +%s%N) - t0) / 1000000 ))
  awk -v tag=$5 -v ms=$ms -v n=$(wc -l < "$3") '/^CHECKED/{f=$5; sub(/\(/,"",f); x=$11} /^JOINED/{j=$2; s=$8; r=$11} END{printf "%s: laws %s free %s not-proved %s joined %s searches %s reached %s ms %s\n", tag, n, f, x, j, s, r, ms}' "$T/$5.log"
}
for fam in add3 sbo3 mix3 cmp3d; do
  S="$R-size-band/size_band/$fam"
  for f in "$S"/held_size_*.txt; do
    z=$(basename "$f" .txt); z=${z#held_size_}
    for v in ${VISITS:-250 500 1000 2000 5000 20000}; do
      serve $fam "$R-gen-warm-fix/mon_1/lib_$fam/rules.txt" "$f" $v "$fam-s$z-v$v"
    done
  done
done
