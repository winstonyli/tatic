#!/bin/bash
# o2: retired instructions of the pin test (salt 1, both sequences), A (two builds) against B (one build, stream_sequences), arms rotated over 2 batches of 2 runs on CPU 4.
M="$(cygpath -m "$LOCALAPPDATA/o2")"; W="$(cygpath -m "$RUN_DIR")"
ic() { # name exe
  powershell -NoProfile -File "$USERPROFILE/.claude/samply/icount.ps1" -Exe "$M/$2" -Runs 2 -Cpu 4 -ExeArgs 'search::stream_sequences_are_pinned,--exact,--ignored' -Out "$W/ic-$1" 2>&1 | sed "s/^/$1\t/"
}
for r in 1 2; do
  if [ $((r % 2)) = 1 ]; then o="A B"; else o="B A"; fi
  for a in $o; do ic "$a-$r" "$a.exe"; done
done
grep -h 'median' "$RUN_DIR/out.log" | tail -4 | tr '\n' ';' > "$RUN_DIR/headline.txt"
