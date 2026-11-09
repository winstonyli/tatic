#!/bin/bash
# The TLB test: `measure_gate_costs` (doubling(1..13), best of 3 in-process) with mimalloc large OS pages on (LP=1, the
# compiled-in default) or off (LP=0, MIMALLOC_ALLOW_LARGE_OS_PAGES=0). Run from the repo root through run.ps1 -Timed with
# EXE set to the release tatic lib test exe; writes headline.txt with doubling_12 and doubling_13 check ms.
set -e
export MIMALLOC_ALLOW_LARGE_OS_PAGES="${LP:?LP=0 or 1}"
"$EXE" --ignored --exact proof::tests::gate::measure_gate_costs --nocapture --test-threads 1 | tee "$RUN_DIR/gate.txt"
line() { grep "^doubling_$1 " "$RUN_DIR/gate.txt" | awk '{print $3}'; }
echo "LP=$LP check ms d11=$(line 11) d12=$(line 12) d13=$(line 13)" > "$RUN_DIR/headline.txt"
