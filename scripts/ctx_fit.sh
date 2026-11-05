#!/bin/bash
# ctx_fit.sh <church-bv exe> <salts> <out file>: fit the Q2 context model (`church-bv ctx-fit`) on the labelled stragglers of the
# stage-0 dump's mines of those salts (`4-10` or a comma list; DUMP_ROOT overrides the ctx-dump run) and write its weights to
# <out file>, which must not exist (weights files are write-once: the arm cache hashes an arm's .exe.env, not the file it names).
# The FIT line goes to $RUN_DIR/headline.txt.
exe=$1; salts=$2; fit_out=$3
[ -f "$exe" ] && [ -n "$salts" ] && [ -n "$fit_out" ] || { echo "usage: ctx_fit.sh <church-bv exe> <salts> <out file>"; exit 2; }
root=${DUMP_ROOT:-$LOCALAPPDATA/claude-runs/tatic/2026-11-01-ctx-dump}
dirs=""
for s in 4 5 6 7 8 9 10; do
  [ -d "$root/s${s}_A" ] || { echo "ctx_fit: $root/s${s}_A missing"; exit 1; }
  dirs="$dirs${dirs:+;}$(cygpath -w "$root/s${s}_A")"
done
export MACHINE_STATE=0
export Q1_DIRS="$dirs" FIT_SALTS="$salts" FIT_OUT="$(cygpath -w "$fit_out")"
out=${RUN_DIR:-.}
"$exe" ctx-fit < /dev/null | tee "$out/fit.txt"
status=${PIPESTATUS[0]}
grep -E '^(FIT|WROTE)' "$out/fit.txt" > "$out/headline.txt" 2>/dev/null
exit "$status"
