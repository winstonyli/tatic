#!/bin/bash
# class_table.sh <exe>: can a learned table of class representatives (docs/tier-cycle.md, "Canonical forms: hand-coded or
# learned", option c) make held-out laws' sides meet with no rules? The exe is HEAD plus patches/class_table.patch (test
# rewrite::class_table_probe). Per table size in SIZES (default "5 7 9 11"; PROBE_MAX caps the classes, default 60000):
# the residue of run 2026-10-22-join-residue, then each family's size-band held-out sets (run 2026-10-22-size-band).
EXE=$1; T="${RUN_DIR:-$TEMP}/class_table"; R="$LOCALAPPDATA/claude-runs/tatic/2026-10-22"
mkdir -p "$T"
files="$(cygpath -w "$R-join-residue/join_residue/residue.txt")"
for f in "$R"-size-band/size_band/*/held_size_*.txt; do files="$files;$(cygpath -w "$f")"; done
for s in ${SIZES:-5 7 9 11}; do
  PROBE_SIZE=$s PROBE_LAWFILES="$files" "$EXE" rewrite::class_table_probe --exact --ignored --nocapture < /dev/null > "$T/size$s.log" 2>&1
  grep -E "^(TABLE|LAWS|MERGES)" "$T/size$s.log" | sed -E 's#^LAWS .*[\\](size_band|join_residue)[\\]#LAWS #'
done
