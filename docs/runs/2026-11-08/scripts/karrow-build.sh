# karrow-build.sh: release church-bv exes before (aeca7a1) and after (986542a) the direct karrow, built in a detached
# worktree (claude-runs/tatic/karrow-wt) sharing the main tree's target dir (disk was too low for a second one), copied to
# claude-runs/tatic/karrow-exes/{a,b}.exe. The exes read data/ from the worktree, so it stays until the count has run
# (remove it then). Launch through run.ps1.
set -eu
root="$LOCALAPPDATA/claude-runs/tatic"
wt="$root/karrow-wt"; out="$root/karrow-exes"; mkdir -p "$out"
[ -d "$wt" ] || git worktree add -q --detach "$wt" aeca7a1
export CARGO_TARGET_DIR="$(git rev-parse --show-toplevel)/target"
for c in aeca7a1:a 986542a:b; do
  git -C "$wt" checkout -q --detach "${c%:*}"
  (cd "$wt" && cargo build --release -j 8 -p church-bv)
  cp "$CARGO_TARGET_DIR/release/church-bv.exe" "$out/${c#*:}.exe"
done
echo "built $(ls "$out" | tr '\n' ' ')" > "$RUN_DIR/headline.txt"
