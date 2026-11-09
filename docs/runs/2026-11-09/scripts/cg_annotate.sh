#!/bin/bash
# a1: where doubling(GATE_D)'s check misses the cache, by source line. Builds the release test exe with debug info, runs
# measure_cachegrind with the check (last level LL, default 16 MB), and writes cachegrind.out and cg_annotate output to OUT.
set -e
repo="/mnt/c/Users/Winston Li/Documents/GitHub/tatic"
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$HOME/tatic-cg-target-debug} CARGO_PROFILE_RELEASE_DEBUG=true
d=${GATE_D:-13}; ll=${LL:-16777216,16,64}; out=${OUT:-$HOME/cg-out}; mkdir -p "$out"
exe=$(cd "$repo" && cargo test --release -p tatic --lib -j 10 --no-run --message-format=json 2>/dev/null \
  | grep -o '"executable":"[^"]*"' | tail -1 | cut -d'"' -f4)
tag="d$d-ll${ll%%,*}"
cd /tmp
GATE_D=$d GATE_CHECK=1 valgrind --tool=cachegrind --cache-sim=yes --I1=32768,8,64 --D1=32768,8,64 --LL=$ll \
  --cachegrind-out-file="$out/cachegrind.$tag.out" "$exe" --ignored --exact proof::tests::gate::measure_cachegrind --nocapture --test-threads=1 2>&1 | tail -12
cg_annotate --show=Dr,D1mr,DLmr,DLmw --sort=DLmr "$out/cachegrind.$tag.out" > "$out/annotate.$tag.txt"
cg_annotate --show=Dr,D1mr,DLmr,DLmw --sort=DLmr --auto=yes --context=0 "$out/cachegrind.$tag.out" > "$out/lines.$tag.txt"
echo "wrote $out/annotate.$tag.txt"
