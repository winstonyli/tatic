#!/usr/bin/env bash
# Round driver for the end-to-end loop (design notes under docs/superpowers/, not in this repository).
#   EXE=<church_bv test exe> [B=150 K=4 OFFSET=0] scripts/loop_stream.sh none|ref|loop OUTDIR
# Batch r is the laws OFFSET+r*B .. OFFSET+(r+1)*B of the add3 sequence (STRIDE, default 7). It is served under the rules in force
# *before* it is mined, so M is what the stream costs when rules arrive as it does.
# Opt-in (default off): WINDOW=cum mines OFFSET..OFFSET+(r+1)*B after batch r; POOL=1 carries the miner's candidates over rounds
# (RULEMINER_SHOW, $out/pool.txt, RULEMINER_EXTRA).
# WARM=<skip>:<laws>[:<phase>] (not with ref) first mines once on that held-out slice (RULEMINER_PHASE selects the residue class of the
# STRIDE sequence: phase 1 at STRIDE=2 is the laws between the served ones), so the stream starts with those rules in force.
# SPLIT=0|1 restricts everything to one structure-based half of the laws (RULEMINER_SHAPE); the WARM mine then uses the other half.
# WARM_RULES=<file> starts with that rule file in force instead of mining a WARM slice (a deterministic warm mine need not be repeated:
# reuse the rules.txt of a finished static run). The loop does not mine after the last batch (it could not change any M), so the final
# rule count is the rules in force at the last batch.
# scripts/rules/reassoc.txt: six general reassociation rules (mined on add3; they also cut mix3 from 136 to 26 machine proofs): use as WARM_RULES.
# SPHASE=<n> serves the residue class n of the STRIDE sequence (default 0), a stream disjoint from the phase-0 one; the loop mines the same residue class it serves; a WARM mine uses its own phase (default 0).
# FAMILY=add3|mix3|sbo3|cmp3|cmp3d (default add3; the three-variable families, THREE_VAR_FAMILIES in tests/church_bv/search.rs) picks the law family; the add3-only options (DEEP3, WARM phase) do nothing for the others.
# RULEMINER_SHAPE_SALT=<string> (exported) selects a different structure-based split; unset keeps the original halves.
# THREADS=<n> (default 2) sizes the miner pool. To share the machine, also pin and lower priority at launch: cmd //c start "" //b //belownormal //affinity 5000 bash <script> (0x5000 = two physical cores, assuming adjacent logical cores are SMT siblings).
# MACHINE_STATE=0 skips the loop's two machine-state probes (about 6 s each); a sweep of loops should record the state once itself (the ignored test `machine_state_line` prints it).
# RULEMINER_SHUFFLE=<salt> (exported, default 0 = off) reorders the three-variable families' sorted law sequence by a hash, so the batches and stride phases are random samples of the family instead of lexicographic ranges.
# CHECK_FAST=1 does the same for serving (no proof building for machine fallbacks, no kernel check, no NFSAME pass); the CHECKED line and M are unchanged.
# RULEMINER_FAST=1 (exported) makes the miner count machine fallbacks without searching for or building their proofs: about 10x faster mining on cmp3d, but approximate (it can pick different rules; M 41 vs 40 on one ref mine). Use it for exploration, not headline numbers. Serving and the M count are unaffected.
set -euo pipefail
mode=$1; out=$2; mkdir -p "$out"
B=${B:-150}; K=${K:-4}; OFFSET=${OFFSET:-0}
: "${EXE:?set EXE}"
export MACHINE_BANNER=0 # one machine-state line per loop (start and end) instead of two per mine and serve, which cost about 5 s each
[ "${MACHINE_STATE:-1}" = 0 ] || echo "loop machine at start: $("$EXE" machine_state_line --ignored --nocapture 2>&1 | grep -m1 "machine state:")" >&2
case "${WINDOW:-}" in ""|cum) ;; *) echo "WINDOW must be empty or cum, got ${WINDOW}" >&2; exit 2 ;; esac
case "${SPLIT:-}" in ""|0|1) ;; *) echo "SPLIT must be 0 or 1, got ${SPLIT}" >&2; exit 2 ;; esac
case "${WARM:-}" in ""|[0-9]*:[0-9]*) ;; *) echo "WARM must be <skip>:<laws>[:<phase>], got ${WARM}" >&2; exit 2 ;; esac
rules="$out/rules.txt"; : > "$rules"; : > "$out/m.tsv"
win="RULEMINER_FAMILY=${FAMILY:-add3} CHECK_FAMILY=${FAMILY:-add3} RULEMINER_DEEP3=${DEEP3:-1} RULEMINER_STRIDE=${STRIDE:-7}"
mc="RULEMINER_PERM=1 RULEMINER_STEPS=40 RULEMINER_THREADS=${THREADS:-2} RULEMINER_ROUNDS=${ROUNDS:-8}"

mine() { # name skip laws [phase] -> appends the chosen rules to $rules
  local extra_env=() extra="$out/extra_$1.txt" shp=${SPLIT:-2}
  if [ "$1" = warm ] && [ -n "${SPLIT:-}" ]; then shp=$((1 - SPLIT)); fi
  if [ "${POOL:-0}" = 1 ]; then # extra candidates: the cumulative pool
    : > "$extra"
    if [ -f "$out/pool.txt" ]; then cat "$out/pool.txt" >> "$extra"; fi
    if [ -s "$extra" ]; then extra_env=("RULEMINER_EXTRA=$extra"); fi
  fi
  if [ "${POOL:-0}" = 1 ]; then extra_env+=(RULEMINER_SHOW=1); fi
  if ! env $win $mc "${extra_env[@]}" RULEMINER_SKIP=$2 RULEMINER_LAWS=$3 RULEMINER_PHASE=${4:-${SPHASE:-0}} RULEMINER_SHAPE=$shp RULEMINER_BASE="$rules" "$EXE" search::rule_miner --ignored --nocapture > "$out/mine_$1.log" 2>&1; then
    echo "loop_stream: rule_miner failed (see $out/mine_$1.log)" >&2; exit 1
  fi
  { grep -E "RULEMINER chosen" "$out/mine_$1.log" | grep -- " -> " | sed 's/.*size): //' >> "$rules"; } || true
  if [ "${POOL:-0}" = 1 ]; then
    { { grep -E "RULEMINER candidate: " "$out/mine_$1.log" | sed 's/.*candidate: //'; } || true; if [ -f "$out/pool.txt" ]; then cat "$out/pool.txt"; fi; } | sort -u > "$out/pool.tmp"
    mv "$out/pool.tmp" "$out/pool.txt"
  fi
}
serve() { # skip -> prints "M laws"
  local line
  line=$(env $win CHECK_FAST=${CHECK_FAST:-0} RULEMINER_PHASE=${SPHASE:-0} RULEMINER_SHAPE=${SPLIT:-2} RULEMINER_SKIP=$1 RULEMINER_LAWS=$B CHECK_RULES="$rules" "$EXE" search::rule_set_kernel_check --ignored --nocapture 2>&1 | grep -E "^CHECKED")
  echo "$line" | sed -E 's/CHECKED ([0-9]+) laws kernel-checked \(([0-9]+) with no whole-term machine proof\), ([0-9]+) not proved/\1 \2 \3/' | awk '{print $1-$2+$3, $1+$3}'
}

if [ "$mode" = ref ]; then mine ref "$OFFSET" $((B * K)); fi
if [ -n "${WARM_RULES:-}" ] && [ "$mode" != ref ]; then
  [ -f "$WARM_RULES" ] || { echo "WARM_RULES file not found: $WARM_RULES" >&2; exit 2; }
  cp "$WARM_RULES" "$rules"
elif [ -n "${WARM:-}" ] && [ "$mode" != ref ]; then IFS=: read -r ws wl wp <<< "$WARM"; mine warm "$ws" "$wl" "${wp:-0}"; fi
total=0
for ((r = 0; r < K; r++)); do
  skip=$((OFFSET + r * B)); t0=$(date +%s)
  read -r m laws < <(serve "$skip")
  printf '%s\t%s\t%s\t%s\t%s\n' "$r" "$m" "$laws" "$(wc -l < "$rules")" "$(( $(date +%s) - t0 ))" >> "$out/m.tsv"
  total=$((total + m))
  if [ "$mode" = loop ] && [ "$r" -lt $((K - 1)) ]; then
    if [ "${WINDOW:-}" = cum ]; then mine "$r" "$OFFSET" $((B * (r + 1))); else mine "$r" "$skip" "$B"; fi
  fi
done
[ "${MACHINE_STATE:-1}" = 0 ] || echo "loop machine at end: $("$EXE" machine_state_line --ignored --nocapture 2>&1 | grep -m1 "machine state:")" >&2
echo "mode=$mode B=$B K=$K offset=$OFFSET total_M=$total rules=$(wc -l < "$rules")"
