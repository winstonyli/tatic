#!/bin/bash
# memo-build.sh <arm>: q1's A/B of memoising every `shift_child` entry. Builds the working tree's release church-bv and
# church-bv's test exe into the main target dir and copies them to claude-runs/tatic/memo-exes/<arm>.exe and <arm>-test.exe
# (A: 1c07141, B: the same with the shared-only bypass dropped). Launch through run.ps1.
set -eu
out="$LOCALAPPDATA/claude-runs/tatic/memo-exes"; mkdir -p "$out"
cargo build --release -j 10 -p church-bv
cp target/release/church-bv.exe "$out/$1.exe"
cargo test -p church-bv --no-run -j 10 2>&1 | tee "$RUN_DIR/testbuild.txt" | tail -3
exe=$(grep -o 'Executable unittests src.lib.rs ([^)]*)' "$RUN_DIR/testbuild.txt" | sed 's/.*(\(.*\))/\1/')
[ -n "$exe" ] || { echo "no test exe in the build output"; exit 1; }
cp "$exe" "$out/$1-test.exe"
echo "built $1 at $(git rev-parse --short HEAD)$(git diff --quiet -- crates || echo -dirty)" > "$RUN_DIR/headline.txt"
