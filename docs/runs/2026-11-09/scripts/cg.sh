#!/bin/bash
# cachegrind data-cache misses for doubling(d), built (c=0) and built plus checked (c=1), last level simulated at 1 MB
# (the 7840U L2) and 16 MB (its L3); the check's misses are c=1 minus c=0. Run in WSL Ubuntu; DS and LLS override the d
# values and last-level configs. REPS (default 1) checks that many times in one process, so REPS=2 less REPS=1 is a
# repeat check's misses, on a region whose arrays and tables already have their capacity (run 2026-11-09-c1-cg-reps).
# Run 2026-11-09-cachegrind-doubling used the same body as probe_cg (../patches/y1-cache-probes.patch).
set -e
export GATE_REPS=${REPS:-1}
repo="/mnt/c/Users/Winston Li/Documents/GitHub/tatic"
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$HOME/tatic-cg-target}
exe=$(cd "$repo" && cargo test --release -p tatic --lib -j 10 --no-run --message-format=json 2>/dev/null \
  | grep -o '"executable":"[^"]*"' | tail -1 | cut -d'"' -f4)
ds=${DS:-"6 7 8 9 10 11 12 13"}
lls=${LLS:-"1048576,16,64 16777216,16,64"}
cd /tmp
for ll in $lls; do
  for d in $ds; do
    for c in 0 1; do
      GATE_D=$d GATE_CHECK=$c valgrind --tool=cachegrind --cache-sim=yes --I1=32768,8,64 --D1=32768,8,64 --LL=$ll \
        --cachegrind-out-file=/dev/null "$exe" --ignored --exact proof::tests::gate::measure_cachegrind --nocapture --test-threads=1 2>&1 \
        | grep -E "D refs|D1  misses|LLd misses|work=" | tr -s ' ' | sed "s/^/ll=$ll d=$d c=$c reps=$GATE_REPS /"
    done
  done
done
