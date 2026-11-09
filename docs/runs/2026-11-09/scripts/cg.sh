#!/bin/bash
# y1 (run 2026-11-09-cachegrind-doubling): cachegrind data-cache misses for doubling(d), built (c=0) and built plus checked
# (c=1), last level simulated at 1 MB (the 7840U L2) and 16 MB (its L3). Needs ../patches/y1-cache-probes.patch applied
# (probe_cg) and a WSL build: CARGO_TARGET_DIR=$HOME/tatic-cg-target cargo test --release -p tatic --lib --no-run; set exe.
exe=$HOME/tatic-cg-target/release/deps/tatic-454134667450135a
ds=${DS:-"6 7 8 9 10 11 12 13"}
lls=${LLS:-"1048576,16,64 16777216,16,64"}
cd /tmp
for ll in $lls; do
  for d in $ds; do
    for c in 0 1; do
      PROBE_D=$d PROBE_CHECK=$c valgrind --tool=cachegrind --cache-sim=yes --I1=32768,8,64 --D1=32768,8,64 --LL=$ll \
        --cachegrind-out-file=/dev/null "$exe" --ignored --exact proof::tests::gate::probe_cg --nocapture --test-threads=1 2>&1 \
        | grep -E "D refs|D1  misses|LLd misses|work=" | tr -s ' ' | sed "s/^/ll=$ll d=$d c=$c /"
    done
  done
done
