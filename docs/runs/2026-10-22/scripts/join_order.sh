#!/bin/bash
# join_order.sh <exe>: does ordering the join by term size (instead of breadth-first layers) buy what a larger visit
# budget buys? The exe is 93c148a plus `docs/runs/2026-10-22/patches/join_size_first.patch`: JOIN_SIZE_FIRST=1 expands
# each side's smallest reached term first, =2 the one with the least depth plus size; 0 (off) is the unchanged search.
# Per family, the salt-1 ref library (run 2026-10-22-gen-warm-fix, mon_1) serves, for each set in SETS (default "A in"):
# A, the size-band's held-out laws of sizes 9 and 11 (run 2026-10-22-size-band, salt 11); in, the mine's own laws; B,
# the held-prune run's disjoint set (salt 21, sizes 9 and 11). Each order in MODES (default "0 1 2") at each JOIN_VISIT
# in VISITS (default "1000 5000"); add3 also without its rule 4. Prints per serve: free laws (no whole-term machine
# proof), not proved, joined, searches, terms reached and wall ms.
EXE=$1; T="${RUN_DIR:-$TEMP}/join_order"; R="$LOCALAPPDATA/claude-runs/tatic/2026-10-22"
mkdir -p "$T"
serve() { # fam rules laws visit sizefirst tag
  local t0=$(date +%s%N)
  JOIN_SIZE_FIRST=$5 JOIN_VISIT=$4 RULEMINER_FAMILY=$1 CHECK_FAMILY=$1 RULEMINER_DEEP3=1 MACHINE_BANNER=0 CHECK_RULES="$(cygpath -w "$2")" CHECK_LAWFILE="$(cygpath -w "$3")" \
    "$EXE" search::rule_set_kernel_check --exact --ignored --nocapture < /dev/null > "$T/$6.log" 2>&1
  local ms=$(( ($(date +%s%N) - t0) / 1000000 ))
  awk -v tag=$6 -v ms=$ms '/^CHECKED/{f=$5; sub(/\(/,"",f); x=$11} /^JOINED/{j=$2; s=$8; r=$11} END{printf "%s: free %s not-proved %s joined %s searches %s reached %s ms %s\n", tag, f, x, j, s, r, ms}' "$T/$6.log"
}
for fam in add3 sbo3 mix3 cmp3d; do
  L="$R-gen-warm-fix/mon_1/lib_$fam"; S="$R-size-band/size_band/$fam"
  cat "$S/held_size_9.txt" "$S/held_size_11.txt" > "$T/$fam.A.txt"
  libs="full"; [ $fam = add3 ] && { sed 4d "$L/rules.txt" > "$T/add3.minus4.txt"; libs="full minus4"; }
  for lib in $libs; do
    rules="$L/rules.txt"; [ $lib = minus4 ] && rules="$T/add3.minus4.txt"
    for set in ${SETS:-A in}; do
      laws="$T/$fam.A.txt"; [ $set = in ] && laws="$L/laws_mine_ref.txt"
      [ $set = B ] && { cat "$R-held-prune/held_prune/$fam/B_9.txt" "$R-held-prune/held_prune/$fam/B_11.txt" > "$T/$fam.B.txt"; laws="$T/$fam.B.txt"; }
      for v in ${VISITS:-1000 5000}; do for o in ${MODES:-0 1 2}; do
        serve $fam "$rules" "$laws" $v $o "$fam-$lib-$set-v$v-$(case $o in 0) echo bfs;; 1) echo size;; 2) echo depthsize;; esac)"
      done; done
    done
  done
done
