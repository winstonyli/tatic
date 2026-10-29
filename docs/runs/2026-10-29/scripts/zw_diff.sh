#!/bin/bash
# docs/runs/2026-10-29/scripts/zw_diff.sh: are the eight zip_word<u8, O> bodies of two exes instruction for instruction
# the same? Dumps each by docs/runs/2026-10-28/scripts/zw_dis.sh, masks addresses (jump targets and literals differ
# between exes), and compares body by body. Prints one line per body that differs, then a count; exits 1 if any differ.
# usage: zw_diff.sh <exeA> <pdbA> <exeB> <pdbB>
DIS="$(dirname "$0")/../../2026-10-28/scripts/zw_dis.sh"
T="$TEMP/zw_diff.$$"; mkdir -p "$T/a" "$T/b"
bash "$DIS" "$1" "$2" "$T/a" > /dev/null
bash "$DIS" "$3" "$4" "$T/b" > /dev/null
same=0; differ=0
for f in "$T/a"/*.s; do
  n=$(basename "$f")
  mask() { sed -E 's/^ *[0-9a-f]+: *//; s/0x[0-9a-f]+/X/g; s/<[^>]*>/<>/g' "$1"; }
  if [ -f "$T/b/$n" ] && cmp -s <(mask "$f") <(mask "$T/b/$n"); then same=$((same+1)); else differ=$((differ+1)); echo "differs: ${n%.s}"; fi
done
echo "$same same, $differ differ, $(cat "$T/a"/*.s | wc -l) instructions"
rm -rf "$T"
[ $differ = 0 ]
