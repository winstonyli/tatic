#!/bin/bash
# class_collect.sh <exe>: is a build's 257 MB commit freed memory that mimalloc (the test binary's allocator) has not
# returned? The exe is 230bc3b plus patches/class_collect.patch (class_growth.patch, plus mi_collect(true) and a commit
# line after each build). Two same-key builds from the class-atoms-c key, no refutation, with mimalloc's large OS pages
# allowed (as the probes ran) and not (as sweep children run, MIMALLOC_ALLOW_LARGE_OS_PAGES=0).
EXE=$1; T="${RUN_DIR:-$TEMP}/class_collect"; mkdir -p "$T"
key="$(cygpath -w "$LOCALAPPDATA/claude-runs/tatic/2026-10-23-class-atoms-c/class_atoms/key.txt")"
for lp in 1 0; do
  MIMALLOC_ALLOW_LARGE_OS_PAGES=$lp PROBE_ADD=none PROBE_REFUTE=0 PROBE_SIZE=9 PROBE_KEY=file PROBE_KEYIN="$key" PROBE_MAX=400000 \
    PROBE_CLAIMS=20000 PROBE_ROUNDS=2 "$EXE" rewrite::key_refine_probe --exact --ignored --nocapture < /dev/null > "$T/large$lp.log" 2>&1
  echo "== large OS pages $lp: exit $?"
  grep -E "^MEM (start|round)|panicked" "$T/large$lp.log"
done
