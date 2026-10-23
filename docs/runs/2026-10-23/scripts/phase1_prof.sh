#!/bin/bash
# phase1_prof.sh <exe>: samply profiles of salt 1's cold cmp3d sweep (`driver::sweep_prof`, patches/phase1_prof.patch,
# debug info), all its processes, with the class table on (arm `on`) and off (arm `off`, `ABLATE=classes` in `<exe>.env`),
# into $RUN_DIR/<arm>: a copy of the exe and its PDB, pcs.json.gz and the samply log. Frames:
# docs/runs/2026-10-18/scripts/prof_named.py "$RUN_DIR/<arm>" "$RUN_DIR/<arm>/bv_prof.exe".
exe=$1; ps1=$(cygpath -w "$USERPROFILE/.claude/samply/profile.ps1"); pdb=$(basename "${exe%.exe}.pdb")
for arm in on off; do
  o="$RUN_DIR/$arm"; mkdir -p "$o"; d=$(cygpath -w "$o")
  cp "$exe" "$o/bv_prof.exe"; cp "${exe%.exe}.pdb" "$o/$pdb"  # the PDB name the exe records, beside it
  [ $arm = off ] && printf 'ABLATE=classes\n' > "$o/bv_prof.exe.env"
  powershell -NoProfile -Command "& '$ps1' -Exe '$d\\bv_prof.exe' -Out '$d\\pcs.json.gz' -ExeArgs 'driver::sweep_prof','--exact','--ignored','--nocapture'" < /dev/null > "$o/samply.log" 2>&1
  echo "$arm: exit $? $(grep -c '^CLASSES ' "$o/samply.log") table builds in the log; $(ls -la "$o/pcs.json.gz" 2>/dev/null | awk '{print $5}') bytes"
done
echo "profiles: on $(ls "$RUN_DIR/on/pcs.json.gz" 2>/dev/null | wc -l), off $(ls "$RUN_DIR/off/pcs.json.gz" 2>/dev/null | wc -l)" > "$RUN_DIR/headline.txt"
