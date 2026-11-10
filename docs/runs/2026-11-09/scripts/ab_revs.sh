#!/bin/bash
# Builds the release tatic lib test exe at two commits, REV_A and REV_B, from one detached worktree ($LOCALAPPDATA/ab-wt,
# removed at the end) into one target dir ($LOCALAPPDATA/ab-tgt, kept for the next pair), and copies them to RUN_DIR as
# A.exe and B.exe for ab.sh. Run from the repo root through run.ps1; JOBS sets the build's -j (default 6).
set -e
wt="$LOCALAPPDATA/ab-wt"; export CARGO_TARGET_DIR="$LOCALAPPDATA/ab-tgt"
a=$(git rev-parse --short "${REV_A:?}"); b=$(git rev-parse --short "${REV_B:?}")
git worktree remove --force "$wt" 2>/dev/null || true
git worktree add -q --detach "$wt" "$a"
exe() { (cd "$wt" && cargo test --release -p tatic --lib -j "${JOBS:-6}" --no-run --message-format=json 2>/dev/null | grep -o '"executable":"[^"]*"' | tail -1 | cut -d'"' -f4); }
cp "$(exe)" "$RUN_DIR/A.exe"
git -C "$wt" checkout -q --detach "$b"
cp "$(exe)" "$RUN_DIR/B.exe"
git worktree remove --force "$wt"
cmp -s "$RUN_DIR/A.exe" "$RUN_DIR/B.exe" && { echo "A.exe and B.exe are the same file" > "$RUN_DIR/headline.txt"; exit 1; }
echo "built A=$a B=$b" > "$RUN_DIR/headline.txt"
