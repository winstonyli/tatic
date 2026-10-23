#!/bin/bash
# opset_sweep.sh <exe>: open_laws.sh's table seed restricted to every set of 2-4 of the seven bit-vector operators, each
# with and without `lt` (182 sets; budget 20000 terms per level, up to 2 growths, 300 laws per bucket). Prints the raw
# probe output, then one line per set sorted by its estimated open laws (held at width 8): seeds, open laws, classified
# unknown+unknown of all classified, distinct functions.
EXE=$1; DIR=$(dirname "$0")
OPS=(add and or xor sub shl1 shr1); N=${#OPS[@]}; SETS=""
for ((m = 1; m < 1 << N; m++)); do
  k=0; s=""
  for ((i = 0; i < N; i++)); do (( m >> i & 1 )) && { k=$((k + 1)); s="$s${s:+,}${OPS[$i]}"; }; done
  (( k >= 2 && k <= 4 )) && SETS="$SETS $s $s,lt"
done
OUT="${RUN_DIR:-$TEMP}/opset_sweep.txt"
OPSETS="$SETS" PER=300 SEEDS=400000 BUDGETS=20000 LEVELS=2 FAMS=table bash "$DIR/open_laws.sh" "$EXE" | tee "$OUT"
echo "== by estimated open laws: set, seeds, open, unknown+unknown/classified, functions"
awk '/^OPS / {if (set) print est, set, seeds, uu "/" cl, fn; set = $2; est = 0; seeds = 0; uu = 0; cl = 0; fn = 0}
  /^TERMS table seeds:/ {seeds = $4}
  /^OPEN / {for (i = 1; i <= NF; i++) if ($i == "est") est += $(i + 1)}
  /^WHY / {s = $0; while (match(s, /"[a-z+]+": [0-9]+/)) {p = substr(s, RSTART, RLENGTH); split(p, q, ": "); cl += q[2]; if (p ~ /unknown\+unknown/) uu += q[2]; s = substr(s, RSTART + RLENGTH)}}
  /^FUNCS / {fn = $3}
  END {if (set) print est, set, seeds, uu "/" cl, fn}' "$OUT" | sort -k1,1nr | awk '{print $2, "seeds " $3, "open " $1, "uu " $4, "functions " $5}'
