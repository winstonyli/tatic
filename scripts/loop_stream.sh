#!/usr/bin/env bash
# Round driver for the end-to-end loop (design notes under docs/superpowers/, not in this repository).
#   EXE=<church_bv test exe> [B=150 K=4 OFFSET=0 PROPOSER=mined] scripts/loop_stream.sh none|ref|loop OUTDIR
# Batch r is the laws OFFSET+r*B .. OFFSET+(r+1)*B of the add3 sequence (STRIDE, default 7). It is served under the rules in force
# *before* it is mined, so M is what the stream costs when rules arrive as it does.
# Opt-in (default off): WINDOW=cum mines OFFSET..OFFSET+(r+1)*B after batch r; POOL=1 carries the miner's candidates over rounds
# (RULEMINER_SHOW, $out/pool.txt, RULEMINER_EXTRA); MODEL=1 adds $PROPOSER_FILE_CMD's lines to the extra candidates (PROPOSER stays mined).
# WARM=<skip>:<laws>[:<phase>] (not with ref) first mines once on that held-out slice (RULEMINER_PHASE selects the residue class of the
# STRIDE sequence: phase 1 at STRIDE=2 is the laws between the served ones), so the stream starts with those rules in force.
# SPLIT=0|1 restricts everything to one structure-based half of the laws (RULEMINER_SHAPE); the WARM mine then uses the other half.
# WARM_RULES=<file> starts with that rule file in force instead of mining a WARM slice (a deterministic warm mine need not be repeated:
# reuse the rules.txt of a finished static run). The loop does not mine after the last batch (it could not change any M), so the final
# rule count is the rules in force at the last batch.
# scripts/rules/reassoc.txt: six general reassociation rules (mined on add3; they also cut mix3 from 136 to 26 machine proofs): use as WARM_RULES.
# SPHASE=<n> serves the residue class n of the STRIDE sequence (default 0), a stream disjoint from the phase-0 one; mining windows use WARM phase only.
# FAMILY=add3|mix3|sbo3 (default add3) picks the law family; the add3-only options (DEEP3, WARM phase) do nothing for the others.
# RULEMINER_SHAPE_SALT=<string> (exported) selects a different structure-based split; unset keeps the original halves.
set -euo pipefail
mode=$1; out=$2; mkdir -p "$out"
B=${B:-150}; K=${K:-4}; OFFSET=${OFFSET:-0}; PROPOSER=${PROPOSER:-mined}
: "${EXE:?set EXE}"
case "${WINDOW:-}" in ""|cum) ;; *) echo "WINDOW must be empty or cum, got ${WINDOW}" >&2; exit 2 ;; esac
case "${SPLIT:-}" in ""|0|1) ;; *) echo "SPLIT must be 0 or 1, got ${SPLIT}" >&2; exit 2 ;; esac
case "${WARM:-}" in ""|[0-9]*:[0-9]*) ;; *) echo "WARM must be <skip>:<laws>[:<phase>], got ${WARM}" >&2; exit 2 ;; esac
rules="$out/rules.txt"; : > "$rules"; : > "$out/m.tsv"
win="RULEMINER_FAMILY=${FAMILY:-add3} CHECK_FAMILY=${FAMILY:-add3} RULEMINER_DEEP3=${DEEP3:-1} RULEMINER_STRIDE=${STRIDE:-7}"
mc="RULEMINER_PERM=1 RULEMINER_STEPS=40 RULEMINER_THREADS=${THREADS:-6} RULEMINER_ROUNDS=${ROUNDS:-8}"

mine() { # name skip laws [phase] -> appends the chosen rules to $rules
  local file_env=() extra_env=() extra="$out/extra_$1.txt" shp=${SPLIT:-2}
  if [ "$1" = warm ] && [ -n "${SPLIT:-}" ]; then shp=$((1 - SPLIT)); fi
  if [ "$PROPOSER" = file ]; then
    $PROPOSER_FILE_CMD "$1" > "$out/cand_$1.txt"
    file_env=(RULEMINER_PROPOSER=file "RULEMINER_PROPOSER_FILE=$out/cand_$1.txt")
  fi
  if [ "${POOL:-0}" = 1 ] || [ "${MODEL:-0}" = 1 ]; then # extra candidates: the cumulative pool and/or the model's lines
    : > "$extra"
    if [ "${POOL:-0}" = 1 ] && [ -f "$out/pool.txt" ]; then cat "$out/pool.txt" >> "$extra"; fi
    if [ "${MODEL:-0}" = 1 ] && [ "$PROPOSER" != file ]; then
      $PROPOSER_FILE_CMD "$1" > "$out/cand_$1.txt"; cat "$out/cand_$1.txt" >> "$extra"
    fi
    if [ -s "$extra" ]; then extra_env=("RULEMINER_EXTRA=$extra"); fi
  fi
  if [ "${POOL:-0}" = 1 ]; then extra_env+=(RULEMINER_SHOW=1); fi
  if ! env $win $mc "${file_env[@]}" "${extra_env[@]}" RULEMINER_SKIP=$2 RULEMINER_LAWS=$3 RULEMINER_PHASE=${4:-0} RULEMINER_SHAPE=$shp RULEMINER_BASE="$rules" "$EXE" search::rule_miner --ignored --nocapture > "$out/mine_$1.log" 2>&1; then
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
  line=$(env $win RULEMINER_PHASE=${SPHASE:-0} RULEMINER_SHAPE=${SPLIT:-2} RULEMINER_SKIP=$1 RULEMINER_LAWS=$B CHECK_RULES="$rules" "$EXE" search::rule_set_kernel_check --ignored --nocapture 2>&1 | grep -E "^CHECKED")
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
echo "mode=$mode proposer=$PROPOSER B=$B K=$K offset=$OFFSET total_M=$total rules=$(wc -l < "$rules")"
