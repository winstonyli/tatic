#!/usr/bin/env bash
# Transfer score of a batch of proposed laws (docs/tier-cycle.md): mine rules from the batch, then count how much they lower M on a
# held-out window of the target family. The kernel's reward for a proposer: difficulty alone is not enough (hard mutants mine rules
# that do not transfer).
#   EXE=<church_bv test exe> FAMILY=<target family> LAWS=<file of lhs = rhs lines> scripts/transfer_score.sh OUTDIR
# BASE=<rules file> is in force for mining and for both M counts (default: no rules). The held-out window is HELD_SKIP (default 2000),
# HELD_LAWS (default 300) of the family's sequence at stride 1; RULEMINER_SHUFFLE=<salt> (exported) orders it. THREADS (default 2) and
# ROUNDS (default 8) size the miner; RULEMINER_FAST=1 (exported) mines approximately, about 10x faster.
# Prints one line: TRANSFER family=.. laws=.. stragglers=.. rules=.. M_before=.. M_after=.. gain=..
set -euo pipefail
out=$1; mkdir -p "$out"
: "${EXE:?set EXE}" "${FAMILY:?set FAMILY}" "${LAWS:?set LAWS}"
base="$out/base.txt"; if [ -n "${BASE:-}" ]; then cp "$BASE" "$base"; else : > "$base"; fi
MACHINE_BANNER=0 RULEMINER_FAMILY=$FAMILY RULEMINER_DEEP3=1 RULEMINER_PERM=1 RULEMINER_STEPS=40 RULEMINER_THREADS=${THREADS:-2} \
  RULEMINER_ROUNDS=${ROUNDS:-8} RULEMINER_BASE="$base" RULEMINER_LAWFILE="$LAWS" "$EXE" search::rule_miner --ignored --nocapture > "$out/mine.log" 2>&1 \
  || { echo "transfer_score: rule_miner failed (see $out/mine.log)" >&2; exit 1; }
{ cat "$base"; grep -E "RULEMINER chosen" "$out/mine.log" | grep -- " -> " | sed 's/.*size): //' || true; } > "$out/rules.txt"
m() { # rules file -> laws of the held-out window that still need a machine proof
  MACHINE_BANNER=0 CHECK_FAST=1 CHECK_FAMILY=$FAMILY CHECK_RULES="$1" RULEMINER_SKIP=${HELD_SKIP:-2000} RULEMINER_LAWS=${HELD_LAWS:-300} \
    "$EXE" search::rule_set_kernel_check --ignored --nocapture 2>&1 | sed -n 's/^CHECKED \([0-9]*\) laws kernel-checked (\([0-9]*\) with.*/\1 \2/p' | awk '{print $1 - $2}'
}
before=$(m "$base"); after=$(m "$out/rules.txt")
echo "TRANSFER family=$FAMILY laws=$(grep -c ' = ' "$LAWS") stragglers=$(grep -c 'RULEMINER straggler' "$out/mine.log") rules=$(( $(wc -l < "$out/rules.txt") - $(wc -l < "$base") )) M_before=$before M_after=$after gain=$(( before - after ))"
