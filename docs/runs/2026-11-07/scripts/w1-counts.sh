#!/bin/bash
# w1 Task 6 step 4: icount batches of 4 (A/A per arm, A/B rotation, fixed-cost per arm), one log.
E='C:\Users\Winston Li\AppData\Local\claude-runs\tatic\w1-exes'
L="$LOCALAPPDATA/claude-runs/tatic/w1-exes/counts.log"
: > "$L"
for b in aa-base:base-test aa-port:port-test ab1-base:base-test ab1-port:port-test ab2-base:base-test ab2-port:port-test fixed-base:base-fixed fixed-port:port-fixed; do
  name=${b%%:*}; exe=${b#*:}
  echo "=== $name $(date +%T)" >> "$L"
  powershell -NoProfile -File "$USERPROFILE\\.claude\\samply\\icount.ps1" -Exe "$E\\$exe.exe" -Runs 4 -Cpu 4 -ExeArgs w_fold_every_encoded_pair < /dev/null >> "$L" 2>&1
  echo "exit $?" >> "$L"
done
echo "=== done $(date +%T)" >> "$L"
