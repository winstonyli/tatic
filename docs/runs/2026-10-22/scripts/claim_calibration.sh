#!/bin/bash
# claim_calibration.sh <exe>: how much is passing random tests worth? (docs/tier-cycle.md, "How much random testing is
# worth"). The exe is HEAD plus patches/claim_calibration.patch (test rewrite::class_table_probe with PROBE_CLAIMS). Per
# key in KEYS (default "0 4 64 exh": that many random width-8 tuples plus the 8 Boolean ones, or exhaustive widths 3 and
# 4), enumerate the table to size 9, sample 20000 of the merges the key proposes, and label each by counterexample or proof.
EXE=$1; T="${RUN_DIR:-$TEMP}/claim_calibration"
mkdir -p "$T"
for k in ${KEYS:-0 4 64 exh}; do
  t0=$(date +%s%N)
  PROBE_SIZE=9 PROBE_KEY=$k PROBE_MAX=400000 PROBE_CLAIMS=20000 PROBE_PROVE_SECS=600 \
    "$EXE" rewrite::class_table_probe --exact --ignored --nocapture < /dev/null > "$T/key$k.log" 2>&1
  rc=$?
  echo "== key $k ($(( ($(date +%s%N) - t0) / 1000000 )) ms, exit $rc)"
  grep -E "^(TABLE|CLAIMS|LABEL|CAL)|panicked" "$T/key$k.log"
done
