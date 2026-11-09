#!/bin/bash
# d1's timed A/B: the check's ms from measure_cachegrind for two test exes, A.exe and B.exe in EXEDIR (the build run's
# folder, run 2026-11-09-d1-ab-build), alternating per round (ABBA order) so drift lands on both. For each d in DS (default 11 13), N rounds
# (default 10) of one process each; writes "d=<d> <arm> <ms>" lines to ab.txt and per d the medians and the paired
# B - A mean with its standard error to headline.txt. Launch through run.ps1 -Timed.
set -e
out="$RUN_DIR/ab.txt"; : > "$out"
one() { "${EXEDIR:?EXEDIR=<build run folder>}/$1.exe" --ignored --exact proof::tests::gate::measure_cachegrind GATE_D=$2 GATE_CHECK=1 --nocapture \
    --test-threads 1 < /dev/null | grep -o "ms=[0-9.]*" | cut -d= -f2 | sed "s/^/d=$2 $1 /" >> "$out"; }
for d in ${DS:-11 13}; do
    for i in $(seq "${N:-10}"); do
        if [ $((i % 2)) = 1 ]; then one A $d; one B $d; else one B $d; one A $d; fi
    done
done
for d in ${DS:-11 13}; do
    awk -v d="d=$d" '$1 == d { v[$2][++n[$2]] = $3 } END {
        for (a in v) { m = n[a]; asort(v[a], s); med[a] = m % 2 ? s[(m+1)/2] : (s[m/2] + s[m/2+1]) / 2 }
        k = n["A"] < n["B"] ? n["A"] : n["B"]
        for (i = 1; i <= k; i++) { x = v["B"][i] - v["A"][i]; t += x; q += x * x }
        mu = t / k; se = sqrt((q / k - mu * mu) / (k - 1))
        printf "%s A %.1f ms, B %.1f ms, B-A %+.1f +- %.1f (n=%d); ", d, med["A"], med["B"], mu, se, k }' "$out"
done | tee "$RUN_DIR/headline.txt"
