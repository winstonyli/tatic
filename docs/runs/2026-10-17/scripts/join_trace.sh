# join_trace.sh <exe> <salt>: one full sweep (stages $STAGES, default "mines own cold pooled") of a build carrying
# patches/join_trace2.patch, with JOIN_TRACE set: one line per join search (found, reached terms, µs, rule-set
# fingerprint, n, k, the pair) into join_trace.<pid> in kk.sh's directory ($RUN_DIR under run.ps1).
exe=$1; s=$2
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
t0=$(date +%s)
JOIN_TRACE="$(cygpath -w "$d")\join_trace" MACHINE_STATE=0 SALT=$s SWEEP="${STAGES:-mines own cold pooled}" SWEEP_OUT="$(cygpath -w "$d")" "$exe" driver::sweep --exact --ignored --nocapture > "$d/log.txt" 2>&1
echo "exit $? secs $(( $(date +%s) - t0 ))"
