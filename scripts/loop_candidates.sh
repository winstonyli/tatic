#!/usr/bin/env bash
# Candidate rules for round $1: samples from the rulelm checkpoint, converted to infix and filtered (experiment script scripts/experiments/exp.sh, not in this repository).
set -euo pipefail
cd "$(dirname "$0")/.."
T="${TEMP:-/tmp}"; r=${1:?round}
d=$(mktemp -d); trap 'rm -rf "$d"' EXIT
# ck_B is the char-mode (RULELM_X=1) model trained with D=64, 2 layers (exp.sh "exp B"); it samples infix directly, so no from_prefix.
if ! RULELM_X=1 RULELM_D=64 RULELM_LAYERS=2 tools/rulelm/target/release/rulelm.exe sample "$T/ck_B.ckpt" 4000 0.8 $((100 + r)) > "$d/raw" 2> "$d/err" \
  || ! python scripts/filter_candidates.py "$d/raw" > "$d/kept" 2>> "$d/err"; then
  cat "$d/err" >&2; echo "loop_candidates: sampling failed" >&2; exit 1
fi
sort -u "$d/kept"
