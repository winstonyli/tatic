#!/bin/bash
# Run 2026-11-09-d1-ab-build ran this from %TEMP%ab_build.sh. Build the release tatic lib test exe at HEAD (A) and with the d1 inst-scratch patch (B); copy both to RUN_DIR; revert.
set -e
export CARGO_TARGET_DIR="$PWD/target/d1ab"
exe() { cargo test --release -p tatic --lib -j 6 --no-run --message-format=json 2>/dev/null | grep -o '"executable":"[^"]*"' | tail -1 | cut -d'"' -f4; }
a=$(exe); cp "$a" "$RUN_DIR/A.exe"
git apply docs/runs/2026-11-09/patches/d1-inst-scratch-spike.patch
b=$(exe); cp "$b" "$RUN_DIR/B.exe"
git apply -R docs/runs/2026-11-09/patches/d1-inst-scratch-spike.patch
git diff --quiet 14fb70a -- crates && echo "built A and B; crates/ matches 14fb70a" > "$RUN_DIR/headline.txt"
