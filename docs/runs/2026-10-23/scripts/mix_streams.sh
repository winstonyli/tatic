#!/bin/bash
# mix_streams.sh <exe>: does rotating over operator sets beat one set at the same total budget? Arm `mix`: every set of
# `SIZES` (space-separated sizes, default 2) of the seven bit-vector operators as separate table-seeded streams at
# `BUDGET` each (default 20000), their open laws' width-8 functions counted together (MIX); with no `SINGLE=0`, arm
# `add,shr1` (the sweep's best pair): one stream at 21 x 20000. Two growths, every law checked (PER large: counts are
# exact, not sampled).
EXE=$1; DIR=$(dirname "$0")
OPS=(add and or xor sub shl1 shr1); MIX=""
for ((m = 1; m < 128; m++)); do
  k=0; s=""
  for ((i = 0; i < 7; i++)); do (( m >> i & 1 )) && { k=$((k + 1)); s="$s${s:+,}${OPS[$i]}"; }; done
  [[ " ${SIZES:-2} " == *" $k "* ]] && MIX="$MIX${MIX:+;}$s"
done
echo "== mix sizes ${SIZES:-2} budget ${BUDGET:-20000}"
OPSETS="$MIX" PER=100000000 SEEDS=400000 BUDGETS=${BUDGET:-20000} LEVELS=2 FAMS=table bash "$DIR/open_laws.sh" "$EXE" | grep -E "^(OPS|FUNCS|MIX)|panic"
[ "${SINGLE:-1}" = 0 ] && exit
echo "== add,shr1 at 420000"
OPSETS="add,shr1" PER=100000000 SEEDS=400000 BUDGETS=420000 LEVELS=2 FAMS=table bash "$DIR/open_laws.sh" "$EXE" | grep -E "^(OPS|TERMS|FUNCS|MIX|WHY)|panic"
