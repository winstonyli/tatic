#!/bin/bash
# memo-count-rot.sh: q1's A/B, the pin test's retired instructions, A (1c07141) against B (every shift memoised), the
# memo-build.sh test exes, arms rotated over 4 batches (ABBA order) of 2 runs on CPU 4; compare medians.
M="$(cygpath -m "$LOCALAPPDATA/claude-runs/tatic/memo-exes")"; W="$(cygpath -m "$RUN_DIR")"
ic() { # name exe
  powershell -NoProfile -File "$USERPROFILE/.claude/samply/icount.ps1" -Exe "$M/$2" -Runs 2 -Cpu 4 -ExeArgs 'streams::stream_sequences_are_pinned,--exact,--ignored' -Out "$W/ic-$1" 2>&1 | sed "s/^/$1\t/"
}
for r in 1 2 3 4; do
  case $r in 1|4) o="a b";; *) o="b a";; esac
  for a in $o; do ic "$a-$r" "$a-test.exe"; done
done
grep -h 'median' "$RUN_DIR/out.log" | tr '\n' ';' > "$RUN_DIR/headline.txt"
