#!/bin/bash
# m2: retired instructions, large pages on (cb, tb) against off (cbf, tbf), arms rotated across batches of 4 on CPU 4.
M="$(cygpath -m "$LOCALAPPDATA/m2")"; W="$(cygpath -m "$RUN_DIR")"
ic() { # name exe args
  powershell -NoProfile -File "$USERPROFILE/.claude/samply/icount.ps1" -Exe "$M/$2" -Runs 4 -Cpu 4 -ExeArgs "$3" -Out "$W/ic-$1" 2>&1 | sed "s/^/$1\t/"
}
SK='--skip,machine::mimalloc_defaults_to_large_pages'
for r in 1 2 3; do
  if [ $((r % 2)) = 1 ]; then o="cb cbf"; else o="cbf cb"; fi
  for a in $o; do ic "$a-$r" "$a.exe" proof-cost-split; done
done
for r in 1 2 3; do
  if [ $((r % 2)) = 1 ]; then o="tb tbf"; else o="tbf tb"; fi
  for a in $o; do ic "$a-$r" "$a.exe" "$SK"; done
done
echo "m2 counts done" > "$RUN_DIR/headline.txt"
