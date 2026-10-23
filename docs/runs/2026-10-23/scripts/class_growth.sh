#!/bin/bash
# class_growth.sh <exe> [<exe-1m>]: why repeated class-table builds in one process grow the commit by about 128 MB each
# (docs/tier-cycle.md, "`shr1` in the class table, its proofs over atoms, and a table's memory"). <exe> is 9730ff8 plus
# patches/class_growth.patch (class_atoms.patch, plus PROBE_ADD and PROBE_REFUTE and a commit line after each round's
# refutation); <exe-1m> adds patches/class_growth_1m.patch (the same with VALUE_BLOCK 1 MB, above the heap's 512 KB
# direct-allocation threshold). Each arm is a fresh process building 5 times from the class-atoms-c key:
#   same         the same key every build, no refutation
#   same-ref     the same key every build, with the refutation loop
#   grow         4 random width-8 inputs added per build, no refutation
#   same-ref-1m  same-ref on <exe-1m>
EXE=$1; EXE1M=$2; T="${RUN_DIR:-$TEMP}/class_growth"
key="$(cygpath -w "$LOCALAPPDATA/claude-runs/tatic/2026-10-23-class-atoms-c/class_atoms/key.txt")"
mkdir -p "$T"
arm() { name=$1; exe=$2; shift 2; t0=$(date +%s%N)
  env "$@" PROBE_SIZE=9 PROBE_KEY=file PROBE_KEYIN="$key" PROBE_MAX=400000 PROBE_CLAIMS=20000 PROBE_ROUNDS=5 \
    "$exe" rewrite::key_refine_probe --exact --ignored --nocapture < /dev/null > "$T/$name.log" 2>&1; rc=$?
  echo "== $name ($(( ($(date +%s%N) - t0) / 1000000 )) ms, exit $rc)"
  grep -E "^(MEM|ROUND)|panicked" "$T/$name.log" | sed -E 's/; map capacity.*//'; }
arm same "$EXE" PROBE_ADD=none PROBE_REFUTE=0
arm same-ref "$EXE" PROBE_ADD=none PROBE_REFUTE=1
arm grow "$EXE" PROBE_ADD=4 PROBE_REFUTE=0
[ -n "$EXE1M" ] && arm same-ref-1m "$EXE1M" PROBE_ADD=none PROBE_REFUTE=1
