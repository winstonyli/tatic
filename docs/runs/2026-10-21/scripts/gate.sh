#!/usr/bin/env bash
# gate.sh <exe> [<base dir>]: the rewrite-context plan's gate (docs/superpowers/plans/2026-10-21-rewrite-context.md) in one
# run, replacing salts_ab.sh, threads_check.sh and miner_snap.sh run in turn (about 28 minutes, mostly re-running the base
# exe and arms that repeat each other; this takes about 8). Rules and outcomes only, no timing: arms run concurrently.
#   phase 1, concurrently: miner_snap.sh against ../miner_snap_base, and SWEEP=cold:cmp3d at LOOP_THREADS=1 on salts 1 3 5
#   phase 2, in turn: SWEEP=cold:cmp3d at the sweep's default LOOP_THREADS=6 on salts 1-5
# Each sweep becomes a snapshot <run dir>/<arm>.txt: per cold loop its cold_cmp3d.tsv row without the seconds column (total
# and per-batch M, rules, exhausted, joined, reached), then its rules.txt. With <base dir>, salt s's snapshot must equal
# <base dir>/s<s>.txt (the base exe's, made once instead of re-run per gate), and each one-thread snapshot its six-thread
# one (whether the miner's choices depend on its scoring workers). Without it, only writes the snapshots (to make a base).
# `gate.sh --snap <sweep out dir>` prints one snapshot. ../gate_base/ is the plan's base exe's (main at 92b4be4),
# snapshots of run 2026-10-21-t3-gate's s*_A arms (its s*_B, Task 3's exe, are byte-equal). A comparison needs a
# non-empty snapshot, so a sweep that writes nothing fails rather than matching an empty base.
# Last line (also headline.txt): what agreed and how many arms failed; exits 1 on any difference or failed arm.
here=$(cd "$(dirname "$0")" && pwd)
snap() { # <sweep out dir>
    for l in 1 2 3; do
        awk -F'\t' -v k="15-$l" '$2 == k' "$1/cold_cmp3d.tsv" | cut -f1-6,8- | grep . || return 1
        cat "$1/cold_cmp3d_cmp3d_${l}_none/rules.txt" || return 1
    done
}
if [ "${1:-}" = --snap ]; then snap "$2"; exit; fi
exe=$1
base=${2:-}
d=$(bash "$here/../../2026-10-12/scripts/kk.sh")
arm() { # <name> <salt> <threads>: one sweep and its snapshot; fails on a non-zero exit or a missing loop
    local o="$d/$1" t0 e
    rm -rf "$o"; mkdir -p "$o"; t0=$(date +%s)
    LOOP_THREADS=$3 MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=$2 SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture < /dev/null > "$o/log.txt" 2>&1
    e=$?
    snap "$o" > "$d/$1.txt" 2> /dev/null || { [ $e = 0 ] && e=no-snapshot; }
    echo "$1: exit $e wall $(( $(date +%s) - t0 )) s"
    [ "$e" = 0 ]
}
failed=0
pids=()
bash "$here/miner_snap.sh" "$exe" "$d/snap" "$here/../miner_snap_base" > "$d/miner_snap.txt" 2>&1 & snap_pid=$!
for s in 1 3 5; do arm t1_s$s $s 1 & pids+=($!); done
for p in "${pids[@]}"; do wait "$p" || failed=$((failed + 1)); done
wait "$snap_pid"; snap_e=$?
cat "$d/miner_snap.txt"
for s in 1 2 3 4 5; do arm s$s $s 6 || failed=$((failed + 1)); done
same_base=0; same_threads=0
if [ -n "$base" ]; then
    for s in 1 2 3 4 5; do
        if [ -s "$d/s$s.txt" ] && diff -q --strip-trailing-cr "$base/s$s.txt" "$d/s$s.txt" > /dev/null; then echo "salt $s: same as base"; same_base=$((same_base + 1)); else echo "salt $s: DIFFERS from base"; fi
    done
fi
for s in 1 3 5; do
    if [ -s "$d/s$s.txt" ] && cmp -s "$d/s$s.txt" "$d/t1_s$s.txt"; then echo "salt $s: one thread same as six"; same_threads=$((same_threads + 1)); else echo "salt $s: one thread DIFFERS from six"; fi
done
[ $snap_e = 0 ] && snaps=same || snaps=DIFFER
line="gate: miner snapshots $snaps; salts same as base in $same_base of $([ -n "$base" ] && echo 5 || echo 0); one thread same as six in $same_threads of 3; $failed of 8 arms failed"
echo "$line" | tee "${RUN_DIR:-$d}/headline.txt"
[ $snap_e = 0 ] && [ $failed = 0 ] && [ $same_threads = 3 ] && { [ -z "$base" ] || [ $same_base = 5 ]; }
