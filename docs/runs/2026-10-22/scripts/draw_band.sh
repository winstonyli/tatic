#!/bin/bash
# draw_band.sh <exe>: does the choice of the generator's laws move the frontier? (ROADMAP v0.3, survey option 3.) The
# size-band laws (`search::size_band_laws`, reverted; the exe needs `docs/runs/2026-10-22/patches/size_band_probe.patch`;
# SB_SALT=11) less every law any of the four draws' salt-1 ref mines mined on, served under each draw's salt-1 ref library
# (draw 0: run 2026-10-22-gen-warm-fix, draws 1-3: 2026-10-22-gen-draw<d>; mon_1). Prints per family, size and draw:
# laws, proved, free (no whole-term machine proof), not proved, exhausted, joined and the free share.
EXE=$1; T="${RUN_DIR:-$TEMP}/draw_band"; B="$LOCALAPPDATA/claude-runs/tatic/2026-10-22"
lib() { [ "$1" = 0 ] && echo "$B-gen-warm-fix/mon_1/lib_$2" || echo "$B-gen-draw$1/mon_1/lib_$2"; }
mkdir -p "$T"
for fam in add3 sbo3 mix3 cmp3d; do
  SB_FAMILY=$fam SB_SALT=11 SB_PER=200 SB_OUT="$(cygpath -w "$T/$fam")" "$EXE" search::size_band_laws --exact --ignored --nocapture < /dev/null 2>&1 | grep -E "^(SIZE|TERMS)"
  : > "$T/$fam.seen"
  for d in 0 1 2 3; do cat "$(lib $d $fam)/laws_mine_ref.txt" "$(lib $d $fam)/laws_extra_ref.txt" >> "$T/$fam.seen"; done
  for f in "$T/$fam"/size_*.txt; do
    k=$(basename "$f" .txt); grep -vxFf "$T/$fam.seen" "$f" > "$T/$fam/held_$k.txt"
    for d in 0 1 2 3; do
      RULEMINER_FAMILY=$fam CHECK_FAMILY=$fam RULEMINER_DEEP3=1 MACHINE_BANNER=0 CHECK_RULES="$(cygpath -w "$(lib $d $fam)/rules.txt")" CHECK_LAWFILE="$(cygpath -w "$T/$fam/held_$k.txt")" \
        "$EXE" search::rule_set_kernel_check --exact --ignored --nocapture < /dev/null > "$T/$fam/${k}_d$d.log" 2>&1
      awk -v fam=$fam -v k=$k -v d=$d -v n=$(grep -c "" "$T/$fam/held_$k.txt") '/^CHECKED/{p=$2; f=$5; sub(/\(/,"",f); x=$11; e=$14} /^JOINED/{j=$2} END{printf "%s %s draw %s: laws %d proved %d free %d not proved %d exhausted %d joined %d free share %.3f\n", fam, k, d, n, p, f, x, e, j, p ? f/p : 0}' "$T/$fam/${k}_d$d.log"
    done
  done
done
