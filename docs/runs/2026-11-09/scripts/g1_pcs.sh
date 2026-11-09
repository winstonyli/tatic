#!/bin/bash
# g1: retired instructions of church-bv's proof-cost-split with the inst memo gated on shared and height > 2 (A, shipped)
# against shared and not a Var (B, height > 0). Builds both from the g1-pcs worktree (../patches/f2-inst-gate-spike.patch,
# its default arm changed per build; large pages compiled off, as m2off.sh), then counts them in 3 batches of 4 on CPU 4, arms rotated.
set -e
wt="/c/Users/Winston Li/Documents/GitHub/tatic/.claude/worktrees/g1-pcs"; out="$LOCALAPPDATA/g1"; mkdir -p "$out"
export CARGO_TARGET_DIR="$out/tgt" CXXFLAGS_x86_64_pc_windows_msvc="-DMI_DEFAULT_ALLOW_LARGE_OS_PAGES=0 -DMI_DEFAULT_ARENA_RESERVE=65536"
in="$(cygpath -m "/c/Users/Winston Li/Documents/GitHub/tatic/docs/runs/2026-11-07/m2-inputs")"
for arm in A:s2 B:s0; do
  # The Samply task passes no env: church-bv reads its inputs from <exe>.env (m2's inputs).
  printf 'CHECK_FAMILY=cmp3d\nCHECK_RULES=%s/rules.txt\nCHECK_LAWFILE=%s/laws_serve_100.txt\n' "$in" "$in" > "$out/${arm%%:*}.exe.env"
  [ -f "$out/${arm%%:*}.exe" ] && [ -z "$REBUILD" ] && continue
  sed -i -E "s/unwrap_or_else\(\|_\| \"s-?[0-9]+\"/unwrap_or_else(|_| \"${arm#*:}\"/" "$wt/crates/tatic-kernel/src/subst.rs"
  grep -q "\"${arm#*:}\".into()" "$wt/crates/tatic-kernel/src/subst.rs"
  (cd "$wt" && cargo build --release -p church-bv --bin church-bv -j 10 2>&1 | tail -1)
  cp "$CARGO_TARGET_DIR/release/church-bv.exe" "$out/${arm%%:*}.exe"
done
M="$(cygpath -m "$out")"; W="$(cygpath -m "$RUN_DIR")"
for r in 1 2 3; do
  if [ $((r % 2)) = 1 ]; then o="A B"; else o="B A"; fi
  for a in $o; do
    powershell -NoProfile -File "$USERPROFILE/.claude/samply/icount.ps1" -Exe "$M/$a.exe" -Runs 4 -Cpu 4 -ExeArgs proof-cost-split -Out "$W/ic-$a-$r" 2>&1 | sed "s/^/$a-$r\t/"
  done
done
echo "g1 counts done" > "$RUN_DIR/headline.txt"
