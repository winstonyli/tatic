#!/bin/bash
# rule_ablation.sh <exe>: does the miner's in-sample score rank rules by what they are worth on held-out laws? (ROADMAP
# v0.5, reward survey option 3's falsifier.) Per family, the salt-1 ref library (run 2026-10-22-gen-warm-fix, mon_1)
# is served whole and then with each rule removed in turn, on its own mine laws (laws_mine_ref, which holds the extras)
# and on the held-out size-9 and size-11 laws of run 2026-10-22-size-band (salt 11, less salt 1's mine laws). The exe
# needs `search::rule_set_kernel_check` (any build; the size-band exe was used). Families run in parallel, one serve at
# a time each. Prints one row per family and rule (index 0 = the whole library): family, index, the miner's logged
# in-sample gain (+N fixed), then free (no whole-term machine proof) and joined counts on in, h9 and h11.
EXE=$1; T="${RUN_DIR:-$TEMP}/rule_ablation"; B="$LOCALAPPDATA/claude-runs/tatic/2026-10-22"
mkdir -p "$T"
serve() { # fam rules laws -> "free joined"
  RULEMINER_FAMILY=$1 CHECK_FAMILY=$1 RULEMINER_DEEP3=1 MACHINE_BANNER=0 CHECK_RULES="$(cygpath -w "$2")" CHECK_LAWFILE="$(cygpath -w "$3")" \
    "$EXE" search::rule_set_kernel_check --exact --ignored --nocapture < /dev/null 2>&1 |
    awk '/^CHECKED/{f=$5; sub(/\(/,"",f)} /^JOINED/{j=$2} END{printf "%s %s", f, j}'
}
fam_run() {
  fam=$1; L="$B-gen-warm-fix/mon_1/lib_$fam"; S="$B-size-band/size_band/$fam"; D="$T/$fam"; mkdir -p "$D"
  grep 'RULEMINER chosen' "$L/mine_ref.log" | sed -E 's/.*\(\+([0-9]+) fixed.*/\1/' > "$D/gain.txt"
  n=$(grep -c '' "$L/rules.txt")
  [ "$(grep -c '' "$D/gain.txt")" = "$n" ] || { echo "$fam: $n rules but $(grep -c '' "$D/gain.txt") chosen lines" >&2; return 1; }
  for i in $(seq 0 "$n"); do
    if [ "$i" = 0 ]; then cp "$L/rules.txt" "$D/rules_0.txt"; g=-; else sed "${i}d" "$L/rules.txt" > "$D/rules_$i.txt"; g=$(sed -n "${i}p" "$D/gain.txt"); fi
    echo "$fam $i $g $(serve $fam "$D/rules_$i.txt" "$L/laws_mine_ref.txt") $(serve $fam "$D/rules_$i.txt" "$S/held_size_9.txt") $(serve $fam "$D/rules_$i.txt" "$S/held_size_11.txt")"
  done > "$D/rows.txt"
}
echo "# fam idx gain in_free in_joined h9_free h9_joined h11_free h11_joined"
for fam in add3 sbo3 mix3 cmp3d; do fam_run $fam & done; wait
cat "$T"/{add3,sbo3,mix3,cmp3d}/rows.txt
