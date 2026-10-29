#!/bin/bash
# pin_prof.sh <exe>: a samply profile of `search::stream_sequences_are_pinned` (both sequences at salt 1, 2 and 4
# growths, STREAM_THREADS default), for the build's shares after a change to the grouping. Into $RUN_DIR: a copy of the
# exe and its PDB, pcs.json.gz, the samply log. Frames: docs/runs/2026-10-18/scripts/prof_named.py "$RUN_DIR" "$RUN_DIR/bv_prof.exe".
exe=$1; ps1=$(cygpath -w "$USERPROFILE/.claude/samply/profile.ps1"); pdb=$(basename "${exe%.exe}.pdb")
o="$RUN_DIR"; d=$(cygpath -w "$o")
cp "$exe" "$o/bv_prof.exe"; cp "${exe%.exe}.pdb" "$o/$pdb"  # the PDB name the exe records, beside it
powershell -NoProfile -Command "& '$ps1' -Exe '$d\\bv_prof.exe' -Out '$d\\pcs.json.gz' -ExeArgs 'search::stream_sequences_are_pinned','--exact','--ignored','--nocapture'" < /dev/null > "$o/samply.log" 2>&1
echo "exit $?; $(wc -c < "$o/pcs.json.gz" 2>/dev/null) bytes; $(grep -c '^PINNED' "$o/samply.log") PINNED lines; $(grep -c 'test result: ok' "$o/samply.log") ok" > "$o/headline.txt"
