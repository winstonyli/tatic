#!/bin/bash
# ctx_q1.sh <church-bv exe> [context-key]: the offline Q1 report (`church-bv q1-report`) on the stage-0 dump (seven arm folders
# s4_A..s10_A of the ctx-dump run, or DUMP_ROOT). The key is space-free so it survives run.ps1's -Command: `full` = the 35-column
# "context" model, `no-g3` (default) = the 33-column model Q2 runs (decision c1). The last verdict lines go to
# $RUN_DIR/headline.txt.
exe=$1
key=${2:-no-g3}
case "$key" in
  full) ctx=context ;;
  no-g3) ctx="drop group 3" ;;
  *) echo "ctx_q1: unknown context key '$key' (full | no-g3)"; exit 2 ;;
esac
root=${DUMP_ROOT:-$LOCALAPPDATA/claude-runs/tatic/2026-11-01-ctx-dump}
dirs=""
for s in 4 5 6 7 8 9 10; do
  [ -d "$root/s${s}_A" ] || { echo "ctx_q1: $root/s${s}_A missing"; exit 1; }
  dirs="$dirs${dirs:+;}$(cygpath -w "$root/s${s}_A")"
done
export MACHINE_STATE=0
export Q1_DIRS="$dirs"
export Q1_CONTEXT="$ctx"
out=${RUN_DIR:-.}
"$exe" q1-report < /dev/null | tee "$out/q1.txt"
status=${PIPESTATUS[0]}
grep -E '^(context model|gate met|verdict)' "$out/q1.txt" | tail -3 > "$out/headline.txt" 2>/dev/null
exit "$status"
