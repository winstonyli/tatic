# r1-build.sh: release exes of r1's parent (c11d0ab) and r1 (89bcef6) for u2's A/B of the score screen, built from a
# detached worktree with its own target dir, copied to claude-runs/tatic/r1-exes/{a,b}.exe. Launch through run.ps1.
# The exes read data/ from the tree they were built in, so the worktree stays until the gate has run (remove it then).
set -eu
root="$LOCALAPPDATA/claude-runs/tatic"
wt="$root/r1-wt"; out="$root/r1-exes"; mkdir -p "$out"
[ -d "$wt" ] || git worktree add -q --detach "$wt" c11d0ab
export CARGO_TARGET_DIR="$root/r1-target"
for c in c11d0ab:a 89bcef6:b; do
  git -C "$wt" checkout -q --detach "${c%:*}"
  (cd "$wt" && cargo build --release -j 6 -p church-bv)
  cp "$CARGO_TARGET_DIR/release/church-bv.exe" "$out/${c#*:}.exe"
done
echo "built $(ls "$out" | tr '\n' ' ')" > "$RUN_DIR/headline.txt"
