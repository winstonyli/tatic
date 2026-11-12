#!/bin/bash
# cold-probe.sh <commit>...: where capturing_closure_loop's cold JIT time rose from v0.8 S2b's 604 us to about 4.7 ms
# (docs/tier-cycle/, "The proved loop form: measurements"). Builds the `execution` bench at each commit in one detached
# worktree (C:\wpt\coldprobe-wt, target C:\wpt\main) and prints its jit_cold_compile_and_verify row, untimed.
set -eu
repo=$(git rev-parse --show-toplevel)
wt=/c/wpt/coldprobe-wt
git -C "$repo" worktree add -q --detach "$wt" "$1"
trap 'git -C "$repo" worktree remove --force "$wt"' EXIT
for c in "$@"; do
  git -C "$wt" checkout -q --detach "$c"
  line=$(cd "$wt" && CARGO_TARGET_DIR='C:\wpt\main' cargo bench -j 10 -p tatic --bench execution --no-run 2>&1 | grep -o 'Executable.*')
  exe=$(cygpath -u "$(echo "$line" | sed 's/.*(\(.*\))/\1/')")
  t=$("$exe" --bench 'capturing_closure_loop/jit_cold' --warm-up-time 1 --measurement-time 3 2>/dev/null | grep 'time:')
  echo "$(git -C "$wt" log --oneline -1 | cut -c1-60) | $t"
done
