# arm_row.sh: sourced by curve.sh. `row` is lifted unchanged from docs/runs/2026-10-28/scripts/salts.sh (lines 6-21, kept there as the record).
R="$LOCALAPPDATA/claude-runs/tatic"
row() { # <label> <arm> <run>@<salt>...: each salt from its run's arm (A or B)
  local l=$1 a=$2 held=0 m=0 rules=0 cpu=0 w=0 ma=0 op=0 bandfiles=() d s line x
  shift 2
  for rs in "$@"; do
    d="$R/${rs%@*}"; s=${rs#*@}
    line=$(grep -E "^salt $s: M" "$d/out.log")
    if [ $a = A ]; then x=$(sed -E 's/.*M A ([0-9]+) B.*held A ([0-9]+) B.*jobcpu A ([0-9.]+) B.*work A interp=0 walk=([0-9]+) match=([0-9]+) op=([0-9]+) B.*/\1 \2 \3 \4 \5 \6/' <<< "$line")
    else x=$(sed -E 's/.*M A [0-9]+ B ([0-9]+);.*held A [0-9]+ B ([0-9]+);.*jobcpu A [0-9.]+ B ([0-9.]+);.* B interp=0 walk=([0-9]+) match=([0-9]+) op=([0-9]+).*/\1 \2 \3 \4 \5 \6/' <<< "$line"); fi
    set -- $x; m=$((m+$1)); held=$((held+$2)); cpu=$(awk -v a=$cpu -v b=$3 'BEGIN{print a+b}'); w=$((w+$4)); ma=$((ma+$5)); op=$((op+$6))
    rules=$((rules + $(awk -F'\t' '{s+=$6} END{print s}' "$d/s${s}_$a/cold_streams.tsv")))
    bandfiles+=("$d/s${s}_$a/held_bands.txt")
  done
  bands=$(cat "${bandfiles[@]}" | awk '$1 != "none" {L[$2]+=$3; F[$2]+=$4; M[$2]+=$5} END{for (b=11;b<=17;b+=2) printf "%.1f ", 1000*M[b]/L[b]; printf "| "; for (b=11;b<=17;b+=2) printf "%.3f ", F[b]/L[b]}')
  printf '%s | %d | %d | %d | %.0f s | %.2f / %.2f / %.2f | %s\n' "$l" $held $m $rules $cpu $(awk -v w=$w -v m=$ma -v o=$op 'BEGIN{print w/1e9, m/1e9, o/1e9}') "$bands"
}
