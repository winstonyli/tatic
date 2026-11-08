#!/bin/bash
# o2: builds church-bv's test exe at the working tree in a separate target and copies it to $LOCALAPPDATA/o2/<arm>.exe (arm: $1).
export CARGO_TARGET_DIR="$LOCALAPPDATA/o2/tgt"
mkdir -p "$LOCALAPPDATA/o2"
cargo test -p church-bv --no-run -j 6 2>&1 | tee "$RUN_DIR/testbuild.txt" | tail -4
exe=$(grep -o 'Executable unittests src.lib.rs ([^)]*)' "$RUN_DIR/testbuild.txt" | sed 's/.*(\(.*\))/\1/')
[ -n "$exe" ] || { echo "no test exe in the build output"; exit 1; }
cp "$exe" "$LOCALAPPDATA/o2/$1.exe" || exit 1
echo "built $1 at $(git rev-parse --short HEAD)$(git diff --quiet -- crates || echo -dirty)" > "$RUN_DIR/headline.txt"
