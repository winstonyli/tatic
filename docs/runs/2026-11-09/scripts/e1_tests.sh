#!/bin/bash
# e1's tests: the kernel in debug (so the instantiate_n re-entry assertion runs), the kernel and wasm crates in release,
# and the tatic crate's gate tests in release. Run from the repo root through run.ps1.
set -e
cargo test -j 6 -p tatic-kernel 2>&1 | grep -E "^test result|FAILED|panicked" 
cargo test --release -j 6 -p tatic-kernel -p tatic-wasm 2>&1 | grep -E "^test result|FAILED|panicked"
cargo test --release -j 6 -p tatic --lib gate 2>&1 | grep -E "^test result|FAILED|panicked"
echo "e1 tests passed" > "$RUN_DIR/headline.txt"
