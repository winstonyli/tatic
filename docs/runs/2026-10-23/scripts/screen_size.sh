#!/bin/bash
# screen_size.sh <exe>: how much of a sweep worker's memory is the screen memo (option 5 of the screen-memo survey).
# The exe is 230bc3b plus patches/screen_size.patch: each worker appends, after every task, its pid, the task, its
# commit and peak commit, and the screen memos' vectors and bytes per (width, variables) to $PROBE_SCREEN_LOG. One
# SWEEP=cold:cmp3d sweep at salt 1 (as salts_ab.sh runs an arm), under `runs run` for peakproc and peakjob.
EXE=$1; T="${RUN_DIR:-$TEMP}/screen_size"; mkdir -p "$T"
runs="$(dirname "$0")/../../../../tools/runs/target/release/runs.exe"
PROBE_SCREEN_LOG="$(cygpath -w "$T/screen.log")" "$runs" run "$(cygpath -w "$T")" -- MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=1 \
  "SWEEP_OUT=$(cygpath -w "$T")" "$EXE" driver::sweep --exact --ignored --nocapture < /dev/null > "$T/result.txt" 2>&1; rc=$?
echo "sweep exit $rc: $(tail -1 "$T/result.txt")"
echo "tasks logged $(wc -l < "$T/screen.log"), workers $(cut -d' ' -f1 "$T/screen.log" | sort -u | wc -l)"
# each worker's last line: its final screen memo against its commit
awk '{last[$1]=$0} END {for (p in last) print last[p]}' "$T/screen.log" | sort -t' ' -k4 -n | cut -c1-300
