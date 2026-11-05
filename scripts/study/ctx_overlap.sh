#!/bin/bash
# ctx_overlap.sh <church-bv exe> <train root> <train salts> <eval root> <eval salts> [eval arms, default "A B"]: how many of the eval
# arms' law texts a model fit on the train folders' labelled slices has seen (`church-bv overlap-report`). Folders are
# <root>/s<salt>_<arm>; train arms are always A (the stage-0 dump). Salts are `4-10` or a comma list. The result line goes to
# $RUN_DIR/headline.txt. Paths and salts carry no spaces (run.ps1 passes -Command through cmd).
exe=$1; troot=$2; tsalts=$3; eroot=$4; esalts=$5; arms=${6:-"A B"}
expand() { case "$1" in *-*) seq "${1%-*}" "${1#*-}" ;; *) echo "$1" | tr ',' ' ' ;; esac; }
join() { local out="" d; for d in "$@"; do out="$out${out:+;}$(cygpath -w "$d")"; done; echo "$out"; }
train=(); eval_=()
for s in $(expand "$tsalts"); do [ -d "$troot/s${s}_A" ] || { echo "ctx_overlap: $troot/s${s}_A missing"; exit 1; }; train+=("$troot/s${s}_A"); done
for s in $(expand "$esalts"); do for a in $arms; do [ -d "$eroot/s${s}_$a" ] || { echo "ctx_overlap: $eroot/s${s}_$a missing"; exit 1; }; eval_+=("$eroot/s${s}_$a"); done; done
export MACHINE_STATE=0
export TRAIN_DIRS="$(join "${train[@]}")" EVAL_DIRS="$(join "${eval_[@]}")"
out=${RUN_DIR:-.}
"$exe" overlap-report < /dev/null | tee "$out/overlap.txt"
status=${PIPESTATUS[0]}
grep '^OVERLAP' "$out/overlap.txt" > "$out/headline.txt" 2>/dev/null
exit "$status"
