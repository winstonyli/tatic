# lazy_prof.sh <exe>: a samply profile of salt 1's cold cmp3d loops on one lane (`driver::sweep_prof`, patches/lazy_prof.patch,
# debug info) into $RUN_DIR: a copy of the exe and its PDB, pcs.json.gz and the samply log. Frames:
# docs/runs/2026-10-12/scripts/prof_self.py "$RUN_DIR".
exe=$1; d=$(cygpath -w "$RUN_DIR"); ps1=$(cygpath -w "$USERPROFILE/.claude/samply/profile.ps1")
cp "$exe" "$RUN_DIR/bv_prof.exe"; cp "${exe%.exe}.pdb" "$RUN_DIR/church_bv-ead98bd4dd1001f2.pdb"  # the name the exe records: samply and llvm-symbolizer look for it beside the exe
powershell -NoProfile -Command "& '$ps1' -Exe '$d/bv_prof.exe' -Out '$d/pcs.json.gz' -ExeArgs 'driver::sweep_prof','--exact','--ignored','--nocapture'" > "$RUN_DIR/samply.log" 2>&1
echo "exit $? $(grep -h 'RULEMINER join:' "$TEMP"/lazy_prof_sweep/cold_cmp3d_*/mine_*.log 2>/dev/null | head -3 | tr '\n' ' ')"
