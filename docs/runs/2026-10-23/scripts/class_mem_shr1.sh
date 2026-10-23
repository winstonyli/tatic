#!/bin/bash
# class_mem_shr1.sh <exe>: the class table with shr1 (spec docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md,
# decision 3 and build step 1). The exe is ddf1eba plus patches/class_mem_shr1.patch (key_refine.patch, plus shr1 as a
# unary operator, commit after each build, the key written to and read from a file, and proofs of the final sample's
# shr1 merges). Run 1 refines a key from the 8 tuples of 0s and 1s with shr1 in the table, normalises the held-out laws,
# proves their replacements and the sampled shr1 merges, and writes the key. Run 2 builds once from that key in a fresh
# process, so its peak commit is the build's alone.
EXE=$1; T="${RUN_DIR:-$TEMP}/class_mem_shr1"; R="$LOCALAPPDATA/claude-runs/tatic/2026-10-22"
mkdir -p "$T"
files="$(cygpath -w "$R-join-residue/join_residue/residue.txt")"
for f in "$R"-size-band/size_band/*/held_size_*.txt; do files="$files;$(cygpath -w "$f")"; done
key="$(cygpath -w "$T/key.txt")"
show() { grep -E "^(ROUND|MEM|FINAL|NOT|LAWS|MERGES|PROVED|SHR)|panicked" "$1" | sed -E 's#^LAWS .*[\](size_band|join_residue)[\]#LAWS #'; }
t0=$(date +%s%N)
PROBE_SIZE=9 PROBE_KEY=0 PROBE_MAX=400000 PROBE_CLAIMS=20000 PROBE_ROUNDS=30 PROBE_PROVE=1 PROBE_SHR=1 PROBE_KEYOUT="$key" \
  PROBE_LAWFILES="$files" "$EXE" rewrite::key_refine_probe --exact --ignored --nocapture < /dev/null > "$T/refine.log" 2>&1; rc=$?
echo "== refine ($(( ($(date +%s%N) - t0) / 1000000 )) ms, exit $rc)"; show "$T/refine.log"
t0=$(date +%s%N)
PROBE_SIZE=9 PROBE_KEY=file PROBE_KEYIN="$key" PROBE_MAX=400000 PROBE_CLAIMS=20000 PROBE_ROUNDS=1 \
  "$EXE" rewrite::key_refine_probe --exact --ignored --nocapture < /dev/null > "$T/build.log" 2>&1; rc=$?
echo "== build from the key file ($(( ($(date +%s%N) - t0) / 1000000 )) ms, exit $rc)"; show "$T/build.log"
