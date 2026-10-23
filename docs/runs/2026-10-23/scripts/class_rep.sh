#!/bin/bash
# class_rep.sh <exe>: the class representative chosen as the smallest member `Machine::parse` takes (option 4 of the
# representative survey; docs/tier-cycle.md, "`shr1` in the class table, its proofs over atoms, and a table's memory").
# The exe is 8ff0c06 plus patches/class_rep.patch (class_growth.patch, plus PROBE_REP=parse and PROBE_KEEP). Each arm
# builds once from the class-atoms-c key in a fresh process, keeps that table, proves the sample's shr1 merges and the
# held-out laws' replacements: `smallest` is today's choice, `parse` the new one.
EXE=$1; T="${RUN_DIR:-$TEMP}/class_rep"; R="$LOCALAPPDATA/claude-runs/tatic/2026-10-22"
key="$(cygpath -w "$LOCALAPPDATA/claude-runs/tatic/2026-10-23-class-atoms-c/class_atoms/key.txt")"
files="$(cygpath -w "$R-join-residue/join_residue/residue.txt")"
for f in "$R"-size-band/size_band/*/held_size_*.txt; do files="$files;$(cygpath -w "$f")"; done
mkdir -p "$T"
arm() { name=$1; shift; t0=$(date +%s%N)
  env "$@" PROBE_SIZE=9 PROBE_KEY=file PROBE_KEYIN="$key" PROBE_MAX=400000 PROBE_CLAIMS=20000 PROBE_ROUNDS=1 PROBE_KEEP=1 \
    PROBE_PROVE=1 PROBE_SHR=1 PROBE_LAWFILES="$files" "$EXE" rewrite::key_refine_probe --exact --ignored --nocapture < /dev/null > "$T/$name.log" 2>&1; rc=$?
  echo "== $name ($(( ($(date +%s%N) - t0) / 1000000 )) ms, exit $rc)"
  grep -E "^(ROUND|REP|SHR|LAWS|MERGES|PROVED|UNPROVED)|panicked" "$T/$name.log" | sed -E 's#^LAWS .*[\](size_band|join_residue)[\]#LAWS #'; }
arm smallest PROBE_REP=smallest
arm parse PROBE_REP=parse
