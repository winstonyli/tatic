#!/usr/bin/env bash
# miner_snap.sh <exe> <outdir>: the miner paths the sweep gate (salts_ab.sh) skips, as timing-free snapshots to diff
# against a base exe's (docs/superpowers/plans/2026-10-21-rewrite-context.md, Task 0). The sweep forces RULEMINER_FAST=1
# and reaches the preference phase only in its pooled stage, so this runs:
#   nonfast1, nonfast4  the non-fast miner (the provable filter's kernel proofs) on 1 and 4 threads, empty base
#   pbase1, pbase4      the same on a base library that carries a preference (Q1: workers prove without it)
#   pooled              driver::sweep's pooled:cmp3d stage: pooled units, then a mine whose only phase is preferences
# Inputs (../miner_snap_inputs): laws_cmp3d_1.txt is the c7 gate's s1_A cold cmp3d loop-1 first mine's law file;
# lib_* and prefs_base.rules are from claude-runs/tatic/2026-10-17-join-cap/v1000_1 (fixed inputs, not current).
# About 5-6 minutes. Output: <outdir>/<config>.txt, plus <outdir>/pooled/ (the sweep's own files).
set -euo pipefail
exe=$1
out=$2
here=$(cd "$(dirname "$0")" && pwd -W 2>/dev/null || pwd)
in="$here/../miner_snap_inputs"
mkdir -p "$out"
# timings and machine-state lines vary run to run; everything else must not
norm() { grep -a '^RULEMINER \|^GEN_\|^mode=' | grep -av '^RULEMINER machine at' | sed -E 's/-?[0-9]+(\.[0-9]+)?(s|ms|µs|ns)\b/T/g'; }
mine() { # <name> <threads> <base>
    MACHINE_STATE=0 RULEMINER_FAMILY=cmp3d RULEMINER_DEEP3=1 RULEMINER_STRIDE=15 RULEMINER_PHASE=1 RULEMINER_SHAPE=2 \
        RULEMINER_PERM=1 RULEMINER_SKIP=0 RULEMINER_LAWS=100 RULEMINER_SHUFFLE=1 RULEMINER_THREADS=$2 \
        RULEMINER_LAWFILE="$in/laws_cmp3d_1.txt" RULEMINER_BASE="$3" \
        "$exe" search::rule_miner --exact --ignored --nocapture < /dev/null > "$out/$1.raw" 2>&1
    norm < "$out/$1.raw" > "$out/$1.txt"
    echo "$1: $(grep -c '^RULEMINER chosen' "$out/$1.txt") chosen"
}
mine nonfast1 1 "$in/empty.rules"
mine nonfast4 4 "$in/empty.rules"
mine pbase1 1 "$in/prefs_base.rules"
mine pbase4 4 "$in/prefs_base.rules"
rm -rf "$out/pooled"
MACHINE_STATE=0 SWEEP=pooled:cmp3d SALT=1 LIB="$in" SWEEP_OUT="$out/pooled" \
    "$exe" driver::sweep --exact --ignored --nocapture < /dev/null > "$out/pooled.raw" 2>&1
{
    norm < "$out/pooled/pooled_cmp3d/mine_ref.log"
    echo "== pooled.units"; cat "$out/pooled/pooled.units"
    echo "== rules.txt"; cat "$out/pooled/pooled_cmp3d/rules.txt"
    echo "== pooled_prefs.tsv (seconds dropped)"; cut -f1,3- "$out/pooled/pooled_prefs.tsv"
    echo "== m.tsv (seconds dropped)"; cut -f1-4,6- "$out/pooled/pooled_cmp3d/m.tsv"
} > "$out/pooled.txt"
echo "pooled: $(grep -c '^RULEMINER prefer' "$out/pooled.txt") preferences"
echo "headline: miner_snap $(ls "$out"/*.txt | wc -l) snapshots in $out"
