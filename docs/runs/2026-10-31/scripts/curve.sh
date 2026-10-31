#!/bin/bash
# curve.sh <label> <A|B> <run name>... : one line per arm summed over its salts, from the gate runs' out.log:
# held-out M, loop M, rules, job CPU, walk/match/op (G), bands 11-17 per 1000 laws | free share. The `row` function of
# docs/runs/2026-10-28/scripts/salts.sh (lines 6-21) is used unchanged.
source <(sed -n 6,21p "$(dirname "$0")/../../2026-10-28/scripts/salts.sh")
label=$1; arm=$2; shift 2
args=(); for r in "$@"; do for s in 1 2 3; do args+=("$r@$s"); done; done
row "$label" "$arm" "${args[@]}"
