# join_ab.sh <exe_a> <exe_b> <salt>...: full sweeps (stages $STAGES, default "mines own cold pooled") of two builds side by side
# per salt, extra environment $ENV_B for b only (e.g. ABLATE=join), into kk.sh's directory ($RUN_DIR under run.ps1): ab_<arm>_<salt>/
# holds the stage files, the log, and the exit code and wall seconds. Prints M per stage file and the wall seconds per arm.
a=$1; b=$2; shift 2
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
for s in "$@"; do
  for arm in a b; do
    (
      o="$d/ab_${arm}_$s"; mkdir -p "$o"; t0=$(date +%s); exe=$a
      if [ "$arm" = b ]; then exe=$b; [ -n "$ENV_B" ] && export $ENV_B; fi
      MACHINE_STATE=0 SALT=$s SWEEP="${STAGES:-mines own cold pooled}" SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1
      echo "$? $(( $(date +%s) - t0 ))" > "$o/exit_secs"
    ) &
  done
  wait
  for arm in a b; do
    o="$d/ab_${arm}_$s"; m=""
    for t in "$o"/*.tsv; do
      [ "$(basename "$t")" = pooled_prefs.tsv ] && continue
      c=4; [ "$(basename "$t")" = mines.tsv ] && c=3
      m="$m $(basename "$t" .tsv) $(awk -F'\t' -v c=$c '{m+=$c} END {print m+0}' "$t")"
    done
    echo "salt $s $arm: M$m, exit+secs $(cat "$o/exit_secs")"
  done
done
