#!/bin/bash
# m2: builds the release church-bv and the test exes at HEAD in a separate target, copies them out for the large-page A/B.
export CARGO_TARGET_DIR="$LOCALAPPDATA/m2/tgt"
mkdir -p "$LOCALAPPDATA/m2"
cargo build --release -p church-bv -j 6 || exit 1
cargo test -p church-bv --no-run -j 6 2>&1 | tee "$RUN_DIR/testbuild.txt" | tail -8
cp "$CARGO_TARGET_DIR/release/church-bv.exe" "$LOCALAPPDATA/m2/cb.exe"
echo "built $(git rev-parse --short HEAD)" > "$RUN_DIR/headline.txt"
