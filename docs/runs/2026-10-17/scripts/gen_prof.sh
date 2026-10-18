# gen_prof.sh <exe>: a samply profile of salt 6's cold cmp3d loop with the non-padding extras, twins dropped
# (`driver::sweep_prof` from patches/gen_prof.patch, on extra_file.patch: a throwaway test that sets the environment,
# since profile.ps1 passes none) into $RUN_DIR: a copy of the exe and its PDB, pcs.json.gz and the samply log. Frames:
# docs/runs/2026-10-12/scripts/prof_self.py "$RUN_DIR".
exe=$1; d=$(cygpath -w "$RUN_DIR"); ps1=$(cygpath -w "$USERPROFILE/.claude/samply/profile.ps1")
cp "$exe" "$RUN_DIR/bv_prof.exe"; cp "${exe%.exe}.pdb" "$RUN_DIR/"
# -Command, not -File: -File passes a comma list as one string
powershell -NoProfile -Command "& '$ps1' -Exe '$d/bv_prof.exe' -Out '$d/pcs.json.gz' -ExeArgs 'driver::sweep_prof','--exact','--ignored','--nocapture'" > "$RUN_DIR/samply.log" 2>&1
echo "exit $? $(grep -h 'RULEMINER join:' "$TEMP"/gen_prof_sweep/cold_cmp3d_*/mine_*.log 2>/dev/null | head -3 | tr '\n' ' ')"
