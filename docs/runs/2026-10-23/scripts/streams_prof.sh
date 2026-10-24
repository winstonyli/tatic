#!/bin/bash
# streams_prof.sh <exe> <salt>: a samply profile of one cold:streams arm as the gate runs it (`driver::sweep`, extras on,
# 2 lanes), all its processes, for the work-count spec (docs/superpowers/specs/2026-10-23-work-counts-design.md): where
# job CPU goes. The environment goes in `<exe>.env` (profile.ps1 passes none; `driver::sweep` reads it through `Setup`).
# Into $RUN_DIR: a copy of the exe and its PDB, pcs.json.gz, the samply log. Frames:
# docs/runs/2026-10-18/scripts/prof_named.py "$RUN_DIR" "$RUN_DIR/bv_prof.exe".
exe=$1; salt=$2; ps1=$(cygpath -w "$USERPROFILE/.claude/samply/profile.ps1"); pdb=$(basename "${exe%.exe}.pdb")
o="$RUN_DIR"; d=$(cygpath -w "$o")
cp "$exe" "$o/bv_prof.exe"; cp "${exe%.exe}.pdb" "$o/$pdb"  # the PDB name the exe records, beside it
printf 'MACHINE_STATE=0\nSWEEP=cold:streams\nSALT=%s\nSWEEP_OUT=%s\n' "$salt" "$d\\sweep" > "$o/bv_prof.exe.env"
powershell -NoProfile -Command "& '$ps1' -Exe '$d\\bv_prof.exe' -Out '$d\\pcs.json.gz' -ExeArgs 'driver::sweep','--exact','--ignored','--nocapture'" < /dev/null > "$o/samply.log" 2>&1
echo "salt $salt: exit $?; $(ls -la "$o/pcs.json.gz" 2>/dev/null | awk '{print $5}') bytes; $(grep -c . "$o/sweep/cold_streams.tsv" 2>/dev/null) tsv rows" > "$o/headline.txt"
