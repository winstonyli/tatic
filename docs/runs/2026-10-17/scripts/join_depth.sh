# join_depth.sh <exe> <salt> <depth>...: full sweeps (stages $STAGES, default "mines own cold pooled") of one build with
# `JOIN_DEPTH=<depth>` (0 = the visit cap) and `JOIN_TRACE` on, two at a time, into kk.sh's directory ($RUN_DIR under
# run.ps1): d<depth>/ holds the stage files, the log, the trace (found, reached, microseconds, meeting depth on each side,
# the pair) and the exit code and wall seconds. Prints M per stage file, searches, met, reached terms and seconds per depth.
exe=$1; s=$2; shift 2
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
run() {
  o="$d/d$1"; mkdir -p "$o"; t0=$(date +%s)
  JOIN_DEPTH=$1 JOIN_TRACE="$(cygpath -w "$o")\\trace" MACHINE_STATE=0 SALT=$s SWEEP="${STAGES:-mines own cold pooled}" SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1 < /dev/null
  echo "$? $(( $(date +%s) - t0 ))" > "$o/exit_secs"
}
while [ $# -gt 0 ]; do
  run "$1" & [ $# -gt 1 ] && { run "$2" & shift; }
  shift; wait
done
for o in "$d"/d*; do
  m=""
  for t in "$o"/*.tsv; do
    [ "$(basename "$t")" = pooled_prefs.tsv ] && continue
    c=4; [ "$(basename "$t")" = mines.tsv ] && c=3
    m="$m $(basename "$t" .tsv) $(awk -F'\t' -v c=$c '{m+=$c} END {print m+0}' "$t")"
  done
  echo "$(basename "$o"): M$m, $(cat "$o"/trace.* | awk -F'\t' '{n++; f+=$1; r+=$2} END {printf "searches %d met %d reached %d", n, f, r}'), exit+secs $(cat "$o/exit_secs")"
done
