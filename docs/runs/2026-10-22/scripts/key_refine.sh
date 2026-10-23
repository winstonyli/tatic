#!/bin/bash
# key_refine.sh <exe>: a class-table key refined by counterexamples (docs/tier-cycle.md, "A key refined by
# counterexamples"). The exe is HEAD plus patches/key_refine.patch (test rewrite::key_refine_probe). Per starting key in
# KEYS (default "0 64 exh"), refine to size 9 on samples of 20000 merges (at most 30 rounds), then normalise the laws of
# run 2026-10-22-join-residue and the size-band held-out sets by the final table and prove its replacements.
EXE=$1; T="${RUN_DIR:-$TEMP}/key_refine"; R="$LOCALAPPDATA/claude-runs/tatic/2026-10-22"
mkdir -p "$T"
files="$(cygpath -w "$R-join-residue/join_residue/residue.txt")"
for f in "$R"-size-band/size_band/*/held_size_*.txt; do files="$files;$(cygpath -w "$f")"; done
for k in ${KEYS:-0 64 exh}; do
  t0=$(date +%s%N)
  PROBE_SIZE=9 PROBE_KEY=$k PROBE_MAX=400000 PROBE_CLAIMS=20000 PROBE_ROUNDS=30 PROBE_PROVE=1 PROBE_LAWFILES="$files" \
    "$EXE" rewrite::key_refine_probe --exact --ignored --nocapture < /dev/null > "$T/key$k.log" 2>&1
  rc=$?
  echo "== key $k ($(( ($(date +%s%N) - t0) / 1000000 )) ms, exit $rc)"
  grep -E "^(ROUND|FINAL|NOT|LAWS|MERGES|PROVED)|panicked" "$T/key$k.log" | sed -E 's#^LAWS .*[\](size_band|join_residue)[\]#LAWS #'
done
