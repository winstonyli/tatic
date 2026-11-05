#!/bin/bash
# curve.sh <label> <A|B> <run name>... : one line per arm summed over its salts, from the gate runs' out.log:
# held-out M, loop M, rules, job CPU, walk/match/op (G), bands 11-17 per 1000 laws | free share (`row` of arm_row.sh).
source "$(dirname "$0")/arm_row.sh"
label=$1; arm=$2; shift 2
args=(); for r in "$@"; do for s in 1 2 3; do args+=("$r@$s"); done; done
row "$label" "$arm" "${args[@]}"
