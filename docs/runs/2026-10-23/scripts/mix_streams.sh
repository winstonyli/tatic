#!/bin/bash
# mix_streams.sh <exe>: does rotating over every pair of the seven bit-vector operators beat one pair at the same total
# budget? Arm `mix`: the 21 pairs as separate table-seeded streams at budget 20000 each, their open laws' width-8
# functions counted together (MIX); arm `add,shr1` (the sweep's best): one stream at 21 x 20000. Two growths, every law
# checked (PER large: counts are exact, not sampled).
EXE=$1; DIR=$(dirname "$0")
OPS=(add and or xor sub shl1 shr1); MIX=""
for ((i = 0; i < 7; i++)); do for ((j = i + 1; j < 7; j++)); do MIX="$MIX${MIX:+;}${OPS[$i]},${OPS[$j]}"; done; done
echo "== mix"
OPSETS="$MIX" PER=100000000 SEEDS=400000 BUDGETS=20000 LEVELS=2 FAMS=table bash "$DIR/open_laws.sh" "$EXE" | grep -E "^(OPS|FUNCS|MIX)|panic"
echo "== add,shr1 at 420000"
OPSETS="add,shr1" PER=100000000 SEEDS=400000 BUDGETS=420000 LEVELS=2 FAMS=table bash "$DIR/open_laws.sh" "$EXE" | grep -E "^(OPS|TERMS|FUNCS|MIX|WHY)|panic"
