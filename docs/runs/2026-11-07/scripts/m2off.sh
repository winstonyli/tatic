#!/bin/bash
# m2: the same exes with large pages compiled off, for counts: the Samply task has its own environment, so the variable cannot reach them.
export CARGO_TARGET_DIR="$LOCALAPPDATA/m2/tgtoff"
export CXXFLAGS_x86_64_pc_windows_msvc="-DMI_DEFAULT_ALLOW_LARGE_OS_PAGES=0 -DMI_DEFAULT_ARENA_RESERVE=65536"
cargo build --release -p church-bv -j 6 || exit 1
cargo test -p church-bv --no-run -j 6 2>&1 | tee "$RUN_DIR/testbuild.txt" | tail -4
cp "$CARGO_TARGET_DIR/release/church-bv.exe" "$LOCALAPPDATA/m2/cbf.exe"
cp "$(grep -oE '[^(]*church_bv-[0-9a-f]+\.exe' "$RUN_DIR/testbuild.txt" | head -1)" "$LOCALAPPDATA/m2/tbf.exe"
ls -la "$LOCALAPPDATA/m2/" 
echo "built off arm $(git rev-parse --short HEAD)" > "$RUN_DIR/headline.txt"
