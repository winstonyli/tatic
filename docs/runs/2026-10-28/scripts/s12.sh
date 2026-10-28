#!/bin/bash
# s12.sh: salts 1-2 of each arm of the mines-budget gates (docs/tier-cycle.md, "A join budget for the mines alone"): held-out M,
# loop M, rules (the summed rules column of each salt's cold_streams.tsv), job CPU, walk/match/op (G), and bands 11-17 per 1000
# laws then free share (held_bands.txt without the table-only `none` lines), from the raw run folders
R="$LOCALAPPDATA/claude-runs/tatic"
row() { # <label> <run> <arm>
  local l=$1 d="$R/$2" a=$3 held=0 m=0 rules=0 cpu=0 w=0 ma=0 op=0
  for s in 1 2; do
    line=$(grep -E "^salt $s: M" "$d/out.log")
    if [ $a = A ]; then x=$(sed -E 's/.*M A ([0-9]+) B.*held A ([0-9]+) B.*jobcpu A ([0-9.]+) B.*work A interp=0 walk=([0-9]+) match=([0-9]+) op=([0-9]+) B.*/\1 \2 \3 \4 \5 \6/' <<< "$line")
    else x=$(sed -E 's/.*M A [0-9]+ B ([0-9]+);.*held A [0-9]+ B ([0-9]+);.*jobcpu A [0-9.]+ B ([0-9.]+);.* B interp=0 walk=([0-9]+) match=([0-9]+) op=([0-9]+).*/\1 \2 \3 \4 \5 \6/' <<< "$line"); fi
    set -- $x; m=$((m+$1)); held=$((held+$2)); cpu=$(awk -v a=$cpu -v b=$3 'BEGIN{print a+b}'); w=$((w+$4)); ma=$((ma+$5)); op=$((op+$6))
    rules=$((rules + $(awk -F'\t' '{s+=$6} END{print s}' "$d/s${s}_$a/cold_streams.tsv")))
  done
  bands=$(cat "$d/s1_$a/held_bands.txt" "$d/s2_$a/held_bands.txt" | awk '$1 != "none" {L[$2]+=$3; F[$2]+=$4; M[$2]+=$5} END{for (b=11;b<=17;b+=2) printf "%.1f ", 1000*M[b]/L[b]; printf "| "; for (b=11;b<=17;b+=2) printf "%.3f ", F[b]/L[b]}')
  printf '%s | %d | %d | %d | %.0f s | %.2f / %.2f / %.2f | %s\n' "$l" $held $m $rules $cpu $(awk -v w=$w -v m=$ma -v o=$op 'BEGIN{print w/1e9, m/1e9, o/1e9}') "$bands"
}
row "base" 2026-10-27-xgrid-f9900h2 A
row "1000,319" 2026-10-28-land-n319 B
row "500,319" 2026-10-28-mjv-j500 B
row "250,319" 2026-10-28-mjv-j250 B
row "100,319" 2026-10-28-mjv-j100 B
row "0,319" 2026-10-28-mjv-j0 B
row "1000,688" 2026-10-27-xgrid-f9900h2 B
row "250,688" 2026-10-28-mjv-j250n688 B
row "100,688" 2026-10-28-mjv-j100n688 B
