#!/bin/bash
# class_table2.sh <exe>: the learned class table with shl1 and lt (a second, one-bit sort), its replacements proved, and
# smaller keys. The exe is HEAD plus patches/class_table2.patch (test rewrite::class_table_probe). Arms (ARMS, default
# all): exh9 = exhaustive key, sizes <= 9, every non-suspect replacement proved and kernel-checked; r64-9, r16-9 = 64 or
# 16 pseudo-random width-8 tuples plus the 8 Boolean ones as the key, sizes <= 9; r64-11 = the same at sizes <= 11.
# Law files: the residue of run 2026-10-22-join-residue, then each family's size-band held-out sets (2026-10-22-size-band).
EXE=$1; T="${RUN_DIR:-$TEMP}/class_table2"; R="$LOCALAPPDATA/claude-runs/tatic/2026-10-22"
mkdir -p "$T"
files="$(cygpath -w "$R-join-residue/join_residue/residue.txt")"
for f in "$R"-size-band/size_band/*/held_size_*.txt; do files="$files;$(cygpath -w "$f")"; done
arm() { # tag size key max prove
  local t0=$(date +%s%N)
  PROBE_SIZE=$2 PROBE_KEY=$3 PROBE_MAX=$4 PROBE_PROVE=$5 PROBE_PROVE_SECS=1200 PROBE_LAWFILES="$files" \
    "$EXE" rewrite::class_table_probe --exact --ignored --nocapture < /dev/null > "$T/$1.log" 2>&1
  local rc=$?
  echo "== $1 ($(( ($(date +%s%N) - t0) / 1000000 )) ms, exit $rc)"
  grep -E "^(TABLE|LAWS|MERGES|PROVED|  slowest)|panicked" "$T/$1.log" | sed -E 's#^LAWS .*[\\](size_band|join_residue)[\\]#LAWS #'
}
for a in ${ARMS:-exh9 r64-9 r16-9 r64-11}; do
  case $a in
    exh9) arm exh9 9 exh 400000 1 ;;
    r64-9) arm r64-9 9 64 400000 0 ;;
    r16-9) arm r16-9 9 16 400000 0 ;;
    r64-11) arm r64-11 11 64 4000000 0 ;;
  esac
done
