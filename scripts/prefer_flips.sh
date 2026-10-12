#!/usr/bin/env bash
# Learn rule preferences for a library (docs/tier-cycle.md, "Rule order"): serve it on phase 0 of each family with RULE_CONFLICTS=1,
# then for each conflicting pair serve with the pair flipped (RULE_PREFER) on phases 0-3, and keep the flips that lower phase 0's M.
#   EXE=<church_bv test exe> LIB=<rules file> scripts/prefer_flips.sh OUTDIR
# RULEMINER_SHUFFLE (default 1) is the salt; WORKERS (default 3) serve in parallel, one thread each. Writes OUTDIR/learned.txt and
# prints `PREFER flips=.. learned=.. train base->learned test base->learned` (train: phase 0, test: phases 1-3; total M of cmp3d,
# add3, sbo3).
set -euo pipefail
out=$1; mkdir -p "$out"
: "${EXE:?set EXE}" "${LIB:?set LIB}"
salt=${RULEMINER_SHUFFLE:-1}; W=${WORKERS:-3}
serve() { # label prefer-file phases.. ; appends `label fam phase M` to $out/m.tsv
  local label=$1 prefer=$2; shift 2
  for fam_stride in cmp3d:15 add3:7 sbo3:11; do
    local fam=${fam_stride%:*} stride=${fam_stride#*:}
    for p in "$@"; do
      local d="$out/run_${label}_${fam}_$p"; rm -rf "$d"
      env ${prefer:+RULE_PREFER=$prefer} ${CONFLICTS:+RULE_CONFLICTS=1} LOOP_MODE=none LOOP_OUT="$d" FAMILY=$fam STRIDE=$stride SPHASE=$p \
        B=100 K=3 CHECK_FAST=1 MACHINE_STATE=0 WARM_RULES="$LIB" RULEMINER_FAST=1 RULEMINER_SHUFFLE=$salt \
        "$EXE" driver::loop_stream --exact --ignored --nocapture > "$d.log" 2>&1 < /dev/null
      echo "$label $fam $p $(sed -n 's/.*total_M=\([0-9]*\).*/\1/p' "$d.log" | tail -1)" >> "$out/m.tsv"
    done
  done
}
rm -f "$out/m.tsv"
CONFLICTS=1 serve base "" 0
serve base "" 1 2 3
# each conflict `winner OVER loser` on phase 0, flipped
cat "$out"/run_base_*_0/serve_*.log | grep "^CONFLICT " | awk '{c=$2; $1=$2=""; s[substr($0, 3)]+=c} END {for (k in s) print s[k] "\t" k}' | sort -rn \
  | cut -f2 | awk -F' OVER ' '{print $2 "  OVER  " $1}' > "$out/flips.txt"
nf=$(wc -l < "$out/flips.txt")
for w in $(seq 0 $((W - 1))); do
  (i=0; while IFS= read -r line; do
    if [ $((i % W)) = "$w" ]; then printf '%s\n' "$line" > "$out/prefer_$i.txt"; serve "$i" "$out/prefer_$i.txt" 0 1 2 3; fi
    i=$((i + 1))
  done < "$out/flips.txt") &
done
wait
total() { awk -v l="$1" -v ph="$2" '$1 == l && (ph == 0 ? $3 == 0 : $3 != 0) {s += $4} END {print s + 0}' "$out/m.tsv"; }
: > "$out/learned.txt"
for i in $(seq 0 $((nf - 1))); do
  [ "$(total "$i" 0)" -lt "$(total base 0)" ] && sed -n "$((i + 1))p" "$out/flips.txt" >> "$out/learned.txt"
done
nl=$(wc -l < "$out/learned.txt")
if [ "$nl" -gt 0 ]; then serve learned "$out/learned.txt" 0 1 2 3; else sed -n 's/^base /learned /p' "$out/m.tsv" >> "$out/m.tsv"; fi
echo "PREFER flips=$nf learned=$nl train $(total base 0)->$(total learned 0) test $(total base 1)->$(total learned 1)"
