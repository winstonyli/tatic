# join_cold.sh <exe> <salt>...: sweeps (stages $STAGES, default cold) of one build with the join on and off (ABLATE=join), the
# two arms of a salt side by side (each loop runs 6 threads), into kk.sh's directory ($RUN_DIR under run.ps1):
# join_<arm>_<salt>/ holds the sweep's stage files (mines.tsv: column 3 is M; the loop stages': column 4), its log and its
# exit code and wall seconds.
exe=$1; shift
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
for s in "$@"; do
  for arm in on off; do
    (
      o="$d/join_${arm}_$s"; mkdir -p "$o"; t0=$(date +%s)
      if [ "$arm" = off ]; then export ABLATE=join; fi
      MACHINE_STATE=0 SALT=$s SWEEP="${STAGES:-cold}" SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1
      echo "$? $(( $(date +%s) - t0 ))" > "$o/exit_secs"
    ) &
  done
  wait
  for arm in on off; do
    o="$d/join_${arm}_$s"; m=""
    for t in "$o"/*.tsv; do
      [ "$(basename "$t")" = pooled_prefs.tsv ] && continue
      c=4; [ "$(basename "$t")" = mines.tsv ] && c=3
      m="$m $(basename "$t" .tsv) $(awk -F'\t' -v c=$c '{m+=$c} END {print m+0}' "$t")"
    done
    echo "salt $s $arm: M$m, exit+secs $(cat "$o/exit_secs")"
  done
done
