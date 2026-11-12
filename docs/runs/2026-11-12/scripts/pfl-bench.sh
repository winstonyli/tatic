#!/bin/bash
# pfl-bench.sh <folder>: one arm of the proved-loop-form A B A bench (plan 2026-11-12-proved-loop-form.md, T5): the
# copied `execution` bench exe in claude-runs\tatic\<folder> on the closure loop's and gcd's groups, criterion's
# 1 s warm-up and 3 s measurement, each group's results in the run's out.log.
set -eu
s="$(dirname "$0")/../../2026-11-11/scripts/v08-exe.sh"
for g in capturing_closure_loop gcd_tail_recursion_to_loop; do
  bash "$s" "$1" --bench "$g/jit" --warm-up-time 1 --measurement-time 3
done
