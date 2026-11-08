#!/bin/bash
# o2 rerun: the pin test's retired instructions, A (two builds) against B (one build), the 2026-11-07 exes, arms rotated over 4 batches (ABBA order) of 2 runs on CPU 4; compare medians.
M="$(cygpath -m "$LOCALAPPDATA/o2")"; W="$(cygpath -m "$RUN_DIR")"
ic() { # name exe
  powershell -NoProfile -File "$USERPROFILE/.claude/samply/icount.ps1" -Exe "$M/$2" -Runs 2 -Cpu 4 -ExeArgs 'search::stream_sequences_are_pinned,--exact,--ignored' -Out "$W/ic-$1" 2>&1 | sed "s/^/$1\t/"
}
for r in 1 2 3 4; do
  case $r in 1|4) o="A B";; *) o="B A";; esac
  for a in $o; do ic "$a-$r" "$a.exe"; done
done
grep -h 'median' "$RUN_DIR/out.log" | tr '\n' ';' > "$RUN_DIR/headline.txt"
