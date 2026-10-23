#!/bin/bash
# size_band.sh <exe>: the frontier falsifier (ROADMAP v0.5). Per family, laws by size from the throwaway probe
# `search::size_band_laws` (reverted; the exe needs `docs/runs/2026-10-22/patches/size_band_probe.patch`) (SB_SALT=11, held out from salt 1's ref mine: lines in its laws_mine_ref/laws_extra_ref are
# dropped), each size served with no mined rules and with the family's salt-1 ref library (run 2026-10-22-gen-warm-fix,
# mon_1). Prints per family, size and rule set: laws, proved, free (no whole-term machine proof), not proved, exhausted,
# joined, and the free share.
EXE=$1; T="${RUN_DIR:-$TEMP}/size_band"; R="$LOCALAPPDATA/claude-runs/tatic/2026-10-22-gen-warm-fix/mon_1"
mkdir -p "$T"; : > "$T/none.txt"
for fam in add3 sbo3 mix3 cmp3d; do
  L="$R/lib_$fam"
  SB_FAMILY=$fam SB_SALT=11 SB_PER=200 SB_OUT="$(cygpath -w "$T/$fam")" "$EXE" search::size_band_laws --exact --ignored --nocapture < /dev/null 2>&1 | grep -E "^(SIZE|TERMS)"
  cat "$L/laws_mine_ref.txt" "$L/laws_extra_ref.txt" > "$T/$fam.seen"
  for f in "$T/$fam"/size_*.txt; do
    k=$(basename "$f" .txt); grep -vxFf "$T/$fam.seen" "$f" > "$T/$fam/held_$k.txt"
    for rs in none ref; do
      rules="$T/none.txt"; [ $rs = ref ] && rules="$L/rules.txt"
      RULEMINER_FAMILY=$fam CHECK_FAMILY=$fam RULEMINER_DEEP3=1 MACHINE_BANNER=0 CHECK_RULES="$(cygpath -w "$rules")" CHECK_LAWFILE="$(cygpath -w "$T/$fam/held_$k.txt")" \
        "$EXE" search::rule_set_kernel_check --exact --ignored --nocapture < /dev/null > "$T/$fam/${k}_$rs.log" 2>&1
      awk -v fam=$fam -v k=$k -v rs=$rs -v n=$(grep -c "" "$T/$fam/held_$k.txt") '/^CHECKED/{p=$2; f=$5; sub(/\(/,"",f); x=$11; e=$14} /^JOINED/{j=$2} END{printf "%s %s %s: laws %d proved %d free %d not proved %d exhausted %d joined %d free share %.2f\n", fam, k, rs, n, p, f, x, e, j, p ? f/p : 0}' "$T/$fam/${k}_$rs.log"
    done
  done
done
