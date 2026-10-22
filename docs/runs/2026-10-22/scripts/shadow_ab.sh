#!/bin/bash
# shadow_ab.sh <exe>: for each case "loopdir|family|shadowed rule", serve each batch after mine 0 with the loop's rule file as served
# (A) and without the shadowed rule (B); prints logged, A and B as M (proved - free + none) and joins.
P="$(cd "$(dirname "$0")" && pwd)"; T="${RUN_DIR:-$TEMP}"; EXE=$1; R="$LOCALAPPDATA/claude-runs/tatic/2026-10-22-gen-warm-fix"
serve() { # rules lawfile family deep3 -> "M joined reached"
  RULEMINER_FAMILY=$3 CHECK_FAMILY=$3 RULEMINER_DEEP3=$4 MACHINE_BANNER=0 CHECK_RULES="$(cygpath -w "$1")" CHECK_LAWFILE="$(cygpath -w "$2")" RULEMINER_SKIP=0 RULEMINER_LAWS=100 \
    "$EXE" search::rule_set_kernel_check --exact --ignored --nocapture < /dev/null 2>&1 \
    | awk '/^CHECKED/{n=$2; k=$5; sub(/\(/,"",k); p=$11} /^JOINED/{j=$2; r=$11} END{print n-k+p, j, r}'
}
while IFS='|' read -r loop fam shadow; do
  L="$R/$loop"; deep=0; [ "$fam" = cmp3d ] && deep=1
  while IFS=$'\t' read -r b m laws cnt secs ex j rc; do
    [ "$b" -ge 1 ] || continue
    head -"$cnt" "$L/rules.txt" > "$T/a.txt"; grep -vxF "$shadow" "$T/a.txt" > "$T/b.txt"
    [ $(wc -l < "$T/a.txt") -eq $(($(wc -l < "$T/b.txt") + 1)) ] || { echo "$loop b$b: shadowed rule not in the first $cnt rules"; continue; }
    skip=$(ls "$L" | grep -oE 'laws_serve_[0-9]+' | sort -t_ -k3 -n | sed -n "$((b + 1))p")
    echo "$loop $fam batch $b ($skip): logged M $m joined $j reached $rc | A $(serve "$T/a.txt" "$L/$skip.txt" $fam $deep) | B $(serve "$T/b.txt" "$L/$skip.txt" $fam $deep)"
  done < "$L/m.tsv"
done < "$P/shadow_cases.txt"
