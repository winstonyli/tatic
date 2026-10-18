# arms_ab.sh <salt> <exe>...: SWEEP=cold:cmp3d at 1 lane with each exe in order and then in reverse (A B C C B A, so
# drift falls on every arm alike), into kk.sh's directory ($RUN_DIR under run.ps1). Prints each sweep's wall seconds, each
# arm's total, and whether each sweep's files agree with the first's (same_arms.sh). A watchdog stops an exe past 8 GB.
s=$1; shift
here=$(dirname "$0")
d=$(bash "$here/../../2026-10-12/scripts/kk.sh")
order=("$@"); for ((j = $# - 1; j >= 0; j--)); do order+=("${@:j+1:1}"); done
i=0
for exe in "${order[@]}"; do
  i=$((i + 1)); name=$(basename "$exe" | sed 's/\.[Ee][Xx][Ee]$//')
  o="$d/${i}_$name"; mkdir -p "$o"; rm -f "$o/exit"; t0=$(date +%s)
  ( SWEEP=cold:cmp3d MACHINE_STATE=0 SALT=$s SWEEP_LANES=1 SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1; echo $? > "$o/exit" ) &
  while [ ! -f "$o/exit" ]; do
    mb=$(powershell -NoProfile -Command "[int]((Get-Process $name -EA 0 | Measure-Object WorkingSet64 -Sum).Sum/1MB)" < /dev/null | tr -d '\r')
    [ "${mb:-0}" -gt 8192 ] && { echo "$i $name: over 8 GB ($mb MB), stopped"; taskkill //F //IM "$name.exe" > /dev/null; }
    ping -n 4 127.0.0.1 > /dev/null
  done
  w=$(( $(date +%s) - t0 )); echo "$w" > "$o/wall"
  echo "$i $name: exit $(cat "$o/exit") wall $w s"
done
first=$(ls -d "$d"/1_* | head -1)
for exe in "$@"; do
  name=$(basename "$exe" | sed 's/\.[Ee][Xx][Ee]$//'); w=0
  for o in "$d"/*_"$name"; do
    w=$(( w + $(cat "$o/wall") ))
    [ "$o" = "$first" ] || echo "$(basename "$o") vs $(basename "$first"): $(bash "$here/../../2026-10-17/scripts/same_arms.sh" "$first" "$o" | tr '\n' ' ')"
  done
  echo "total $name: wall $w s"
done
