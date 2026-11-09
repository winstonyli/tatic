#!/bin/bash
# f2/f3: the inst memo's gate under the per-call memo (f0e6b09), counted by cachegrind. Builds REPO (a worktree with
# ../patches/f2-inst-gate-spike.patch, knob INST_GATE: s<k> shared and height > k, a<k> any node, k = -1 no cutoff) once
# with debug info, then runs measure_cachegrind per arm, d and last level, P at a time; prints I refs, D refs, misses and
# work per line. The s2 (shipped) arm at d = 13, 16 MB keeps cachegrind.out for REPS 1 and 2 in OUT, for f3's annotation.
# ARMS runs only those arms' checks. Run from a copy in WSL home (a path with a space broke run.ps1's quoting).
set -e
repo=${REPO:-"/mnt/c/Users/Winston Li/Documents/GitHub/tatic/.claude/worktrees/f2-gate"}
export CARGO_TARGET_DIR=$HOME/f2-cg-target CARGO_PROFILE_RELEASE_DEBUG=true
export OUT=${OUT:-$HOME/f2-out}; rm -rf "$OUT"; mkdir -p "$OUT/parts"
export exe=$(cd "$repo" && cargo test --release -p tatic --lib -j 10 --no-run --message-format=json 2>/dev/null \
  | grep -o '"executable":"[^"]*"' | tail -1 | cut -d'"' -f4)
one() { # arm d ll c reps keep
  local tag="$1-d$2-ll${3%%,*}-c$4-r$5" f=/dev/null
  [ "$6" = 1 ] && f="$OUT/cachegrind.$tag.out"
  cd /tmp && INST_GATE=$1 GATE_D=$2 GATE_CHECK=$4 GATE_REPS=$5 valgrind --tool=cachegrind --cache-sim=yes \
    --I1=32768,8,64 --D1=32768,8,64 --LL=$3 --cachegrind-out-file=$f "$exe" --ignored --exact \
    proof::tests::gate::measure_cachegrind --nocapture --test-threads=1 2>&1 \
    | grep -E "I *refs|D *refs|D1 *misses|LLd misses|work=" | tr -s ' ' | sed "s/^/$tag /" > "$OUT/parts/$tag.txt"
}
export -f one
M=1048576,16,64; G=16777216,16,64
{ for a in ${ARMS:-s2 s-1 s1 s3 a2 a-1}; do for d in 11 13; do for ll in $M $G; do k=0; [ -z "$ARMS" ] && [ "$a$d$ll" = "s213$G" ] && k=1; echo "$a $d $ll 1 1 $k"; done; done; done
  [ -n "$ARMS" ] || { for a in s2 a-1; do for d in 11 13; do echo "$a $d $G 0 1 0"; done; done; echo "s2 13 $G 1 2 1"; }; } | xargs -P ${P:-8} -L 1 bash -c 'one "$@"' _
cat "$OUT"/parts/*.txt
