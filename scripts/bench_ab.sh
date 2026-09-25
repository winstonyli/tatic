#!/usr/bin/env bash
# A/B benchmark: a base revision against the working tree, then the base
# again as a noise check. On this laptop a re-run of unchanged code moves
# benches by up to ±100% (RELATED_WORK.md §49, §51), so a change is real
# only where candidate-vs-base clearly exceeds base-again-vs-base.
#
#   scripts/bench_ab.sh [REV] [cargo bench args] [-- criterion args]
#   scripts/bench_ab.sh HEAD --bench proofs
#   scripts/bench_ab.sh main~3 --bench execution -- fib
#
# REV (default HEAD) is checked out in a worktree under target/bench-ab,
# with its own target dir, so the working tree is never touched and
# uncommitted and untracked files are all in the candidate. The first
# run builds the dependencies there once.
set -euo pipefail

# Below-normal priority, inherited by cargo and the benches. Windows
# ignores nice, so set this shell's own priority class. (Re-launching
# through `cmd //c start //belownormal` would let cmd re-parse the
# arguments, and a criterion filter like 'a|b' would become a pipe.)
if [ -r /proc/$$/winpid ]; then
  powershell -NoProfile -Command \
    "(Get-Process -Id $(cat /proc/$$/winpid)).PriorityClass = 'BelowNormal'"
else
  renice -n 10 $$ >/dev/null 2>&1 || true
fi
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-12}"

repo=$(git rev-parse --show-toplevel)
rev=HEAD
if [ $# -gt 0 ] && [ "${1#-}" = "$1" ]; then rev=$1; shift; fi
commit=$(git -C "$repo" rev-parse --verify "$rev^{commit}")

cargo_args=(); crit_args=()
while [ $# -gt 0 ]; do
  if [ "$1" = -- ]; then shift; crit_args=("$@"); break; fi
  cargo_args+=("$1"); shift
done
# Without a target, cargo also runs the lib's test harness, which rejects
# criterion's flags; select every bench target instead.
case " ${cargo_args[*]} " in
  *" --bench"*) ;;
  *) cargo_args+=(--bench '*') ;;
esac

ab=$repo/target/bench-ab
base=$ab/base
export CRITERION_HOME=$ab/criterion
git -C "$repo" worktree prune
if [ -e "$base/.git" ]; then
  git -C "$base" checkout -q -f --detach "$commit"
else
  git -C "$repo" worktree add -q --detach "$base" "$commit"
fi

run() { # dir log criterion-flags...
  local dir=$1 log=$2 st=0; shift 2
  (cd "$dir" && CARGO_TARGET_DIR="${target:-$dir/target}" \
    cargo bench "${cargo_args[@]}" -- "${crit_args[@]}" "$@") > "$log" 2>&1 || st=$?
  grep -E "^[A-Za-z0-9_/]+$|time:|change:|^error" "$log" || true
  if [ $st -ne 0 ]; then echo "cargo bench failed ($st); see $log"; fi
  return $st
}

echo "=== base $(git -C "$repo" log -1 --format='%h %s' "$commit")"
target=$ab/target run "$base" "$ab/base.log" --save-baseline base
echo "=== candidate (working tree)"
target= run "$repo" "$ab/candidate.log" --baseline base
echo "=== base again (noise)"
target=$ab/target run "$base" "$ab/noise.log" --baseline base

# Middle estimate per bench, in ns. Criterion prints the name on its own
# line when it's long, else on the time: line.
times() {
  awk '/time:/ { if ($1 != "time:") name = $1
                 for (i = 1; i <= NF; i++) if ($i ~ /^\[/) break
                 v = $(i + 2); u = $(i + 3)
                 m = u == "ns" ? 1 : u == "ms" ? 1e6 : u == "s" ? 1e9 : 1e3
                 print name, v * m; next }
       /^[A-Za-z0-9_\/]+$/ { name = $1 }' "$1"
}
echo "=== summary (candidate and noise relative to base)"
awk 'function fmt(ns) { return ns >= 1e6 ? sprintf("%.2f ms", ns / 1e6) : sprintf("%.1f us", ns / 1e3) }
     FILENAME == ARGV[1] { b[$1] = $2; order[++n] = $1; next }
     FILENAME == ARGV[2] { c[$1] = $2; next }
     { z[$1] = $2 }
     END { printf "%-60s %10s %10s %8s %8s\n", "bench", "base", "cand", "cand", "noise"
           for (i = 1; i <= n; i++) { k = order[i]
             printf "%-60s %10s %10s %+7.0f%% %+7.0f%%\n", k, fmt(b[k]), fmt(c[k]),
                    100 * (c[k] / b[k] - 1), 100 * (z[k] / b[k] - 1) } }' \
  <(times "$ab/base.log") <(times "$ab/candidate.log") <(times "$ab/noise.log")
echo "logs: $ab/{base,candidate,noise}.log"
