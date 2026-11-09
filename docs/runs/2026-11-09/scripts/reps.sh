#!/bin/bash
# c2's falsifier: does a check on a region whose arrays and tables already have their capacity (a repeat check: `scoped`
# keeps capacity when it closes) run faster than the first check, which grows them? For each d in DS (default 11 13), N
# processes (default 8; run 2026-11-09-c2-reps-b set N=10) of `measure_cachegrind` with 3 checks each; writes the ms
# lines to reps.txt and the medians of the first check and of the repeats to headline.txt. Run from the repo root
# through run.ps1 with EXE set to the release tatic lib test exe. Untimed: the comparison is paired within each process.
set -e
out="$RUN_DIR/reps.txt"; : > "$out"
for d in ${DS:-11 13}; do
    for i in $(seq "${N:-8}"); do
        "$EXE" --ignored --exact proof::tests::gate::measure_cachegrind GATE_D=$d GATE_CHECK=1 GATE_REPS=3 --nocapture \
            --test-threads 1 < /dev/null | grep -o "ms=[0-9.]*" | cut -d= -f2 | paste -sd' ' | sed "s/^/d=$d /" >> "$out"
    done
done
med() { sort -n | awk '{a[NR]=$1} END {print (NR % 2 ? a[(NR+1)/2] : (a[NR/2] + a[NR/2+1]) / 2)}'; }
for d in ${DS:-11 13}; do
    first=$(grep "^d=$d " "$out" | awk '{print $2}' | med)
    rest=$(grep "^d=$d " "$out" | awk '{print $3; print $4}' | med)
    printf 'd=%s first %s ms, repeats %s ms; ' "$d" "$first" "$rest"
done | tee "$RUN_DIR/headline.txt"
cat "$out"
