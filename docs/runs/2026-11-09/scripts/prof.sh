#!/bin/bash
# c1, where the check's time past linear goes: xperf traces (sampled stacks, faults, allocations) of `measure_cachegrind`
# for each d:checks pair in DS (default d = 11 48 times, d = 13 12 times), large pages on. Run from the repo root through
# run.ps1 -Kind profile with EXE set to the release tatic lib test exe built with CARGO_PROFILE_RELEASE_DEBUG=true; copies
# it and its PDB into RUN_DIR and traces each d. prof_report.sh then writes the reports and prof_agg.py reads them.
set -e
cp "$EXE" "${EXE%.exe}.pdb" "$RUN_DIR/"
X="$RUN_DIR/$(basename "$EXE")"
P="$USERPROFILE/.claude/samply/profile.ps1"
for dr in ${DS:-11:48 13:12}; do
    d=${dr%:*} r=${dr#*:}
    powershell -NoProfile -File "$P" -Mode xperf -Exe "$X" -Out "$RUN_DIR/d$d.etl" \
        -ExeArgs "--ignored,--exact,proof::tests::gate::measure_cachegrind,GATE_D=$d,GATE_CHECK=1,GATE_REPS=$r,--nocapture,--test-threads,1" \
        | tee "$RUN_DIR/d$d.log"
done
echo "traced d:checks ${DS:-11:48 13:12}" > "$RUN_DIR/headline.txt"
