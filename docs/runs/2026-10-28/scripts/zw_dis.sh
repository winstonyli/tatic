#!/bin/bash
# docs/runs/2026-10-28/scripts/zw_dis.sh: per zip_word<u8, O> function in an exe: size, instruction count, and the mix of scalar byte vs packed byte ops.
# A body ends at the next public function or the first int3 padding, whichever comes first.
# usage: zw_dis.sh <exe> <pdb> [dumpdir]
exe="$1"; pdb="$2"; dump="$3"
names=(add and or xor sub lt shl1 shr1)
T="$TEMP/zw_dis.$$"; mkdir -p "$T"
llvm-pdbutil dump --publics "$pdb" 2>/dev/null > "$T/pub.txt"
grep --no-group-separator -A1 'zip_wordhKj' "$T/pub.txt" | paste - - |
  sed -nE 's/.*zip_wordhKj([0-9])_.*addr = 0001:([0-9]+).*/\1 \2/p' | sort -n > "$T/syms.txt"
grep -oE 'flags = function, addr = 0001:[0-9]+' "$T/pub.txt" | grep -oE '[0-9]+$' | sort -n -u > "$T/starts.txt"
printf '%-5s %6s %6s %7s %7s %s\n' op bytes insns movzbl packedB 'top vector ops'
while read -r o off; do
  next=$(awk -v a="$off" '$1 > a { print; exit }' "$T/starts.txt")
  lo=$(printf '0x%x' $((0x140001000 + off))); hi=$(printf '0x%x' $((0x140001000 + next)))
  llvm-objdump -d --no-show-raw-insn --start-address=$lo --stop-address=$hi "$exe" |
    awk 'NF>=2 && $1 ~ /:$/ { if ($2 == "int3") exit; print }' > "$T/body.txt"
  [ -n "$dump" ] && cp "$T/body.txt" "$dump/${names[$o]}.s"
  awk '{print $2}' "$T/body.txt" > "$T/ops.txt"
  n=$(wc -l < "$T/ops.txt")
  mz=$(grep -c '^movzbl$' "$T/ops.txt")
  pb=$(grep -cE '^(paddb|psubb|pcmpgtb|pcmpeqb|pminub|pmaxub|pand|por|pxor|pandn|psllw|psrlw|paddw|pavgb)$' "$T/ops.txt")
  top=$(grep -E '^(p|mov(dq|aps|ups))' "$T/ops.txt" | sort | uniq -c | sort -rn | head -6 | awk '{printf "%s:%s ", $2, $1}')
  printf '%-5s %6d %6d %7d %7d %s\n' "${names[$o]}" "$(( $(tail -1 "$T/body.txt" | awk '{print strtonum("0x" substr($1,1,length($1)-1))}') - lo ))" "$n" "$mz" "$pb" "$top"
done < "$T/syms.txt"
rm -rf "$T"
