#!/bin/bash
# q2_arms.sh <test exe> <out dir> [m...]: the Q2 arms (docs/superpowers/plans/2026-11-01-ctx-scorer-q2.md), each an exe copy
# <out dir>/<name>.exe plus <name>.exe.env (NAME=value lines, which the exe reads and the gate hashes), for n in {80, 160},
# weights w in {4-10, 7-10} and draws d in {0, 3, 4}:
#   s<n>_d<d>        EXTRAS_N=<n> POOL=4 EXTRAS_SELECT=small
#   c<n>_<w>         the same with EXTRAS_SELECT=ctx CTX_WEIGHTS=<weights file> (d = 0), and c<n>_<w>_d<d> for d in {3, 4}
#   r<m>_d<d>        EXTRAS_N=<m>, the random arm of an equal-work comparison, for each m given
# GEN_DRAW=<d> is added when d > 0. The weights file is write-once (the arm cache hashes the .env, not the file it names), so a
# refit gets a new name and new arms. The weights path is the directory in 8.3 form plus the file name, forward slashes: a path with a space would split (the file name stays whole so records and hashes read it).
# WEIGHTS_DIR overrides docs/runs/2026-11-01/ctx-weights (the check script's fixture).
exe=$1; out=$2; shift 2
[ -f "$exe" ] && [ -n "$out" ] || { echo "usage: q2_arms.sh <test exe> <out dir> [m...]"; exit 2; }
dir=${WEIGHTS_DIR:-"$(cd "$(dirname "$0")/.." && pwd)/docs/runs/2026-11-01/ctx-weights"}
mkdir -p "$out"
arm() { # <name> <env lines...>
  local name=$1; shift
  cp "$exe" "$out/$name.exe"
  printf '%s\n' "$@" > "$out/$name.exe.env"
}
draw() { [ "$1" -gt 0 ] && echo "GEN_DRAW=$1"; return 0; }
for n in 80 160; do
  for d in 0 3 4; do
    arm "s${n}_d$d" "EXTRAS_N=$n" "POOL=4" "EXTRAS_SELECT=small" $(draw $d)
  done
  for w in 4-10 7-10; do
    f="$dir/ctx33-v1-s$w.txt"
    [ -f "$f" ] || { echo "q2_arms: weights file $f missing"; exit 1; }
    path="$(cygpath -m "$(cygpath -d "$dir")")/ctx33-v1-s$w.txt"
    case "$path" in *" "*) echo "q2_arms: weights path has a space: $path"; exit 1 ;; esac
    for d in 0 3 4; do
      name="c${n}_$w"; [ $d -gt 0 ] && name="${name}_d$d"
      arm "$name" "EXTRAS_N=$n" "POOL=4" "EXTRAS_SELECT=ctx" "CTX_WEIGHTS=$path" $(draw $d)
    done
  done
done
for m in "$@"; do
  for d in 0 3 4; do arm "r${m}_d$d" "EXTRAS_N=$m" $(draw $d); done
done
