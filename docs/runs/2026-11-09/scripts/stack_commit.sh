#!/bin/bash
# stack_commit.sh: a sweep's peak commit with task threads and lanes on the check stack (HEAD) against default stacks
# (REV_A's entry.rs and driver.rs checked out over HEAD for one build, then restored). Builds release church-bv twice
# in the repo's target, runs the gate's sweep at salt 1 ROUNDS times per arm (A B A B), and prints each result line
# (peakproc is the largest process's peak commit). Run from the repo root, crates clean, through run.ps1; JOBS is the -j.
set -e
files="crates/church-bv/src/entry.rs crates/church-bv/src/driver.rs"
[ -z "$(git status --porcelain -- crates)" ] || { echo "crates not clean"; exit 1; }
. scripts/gate/arm_env.sh
runs="tools/runs/target/release/runs.exe"
build() { cargo build --release -p church-bv -j "${JOBS:-6}" 2>&1 | tail -1; cp target/release/church-bv.exe "$RUN_DIR/$1.exe"; }
build B
trap 'git checkout -q HEAD -- $files' EXIT
git checkout -q "${REV_A:?}" -- $files
build A
git checkout -q HEAD -- $files; trap - EXIT
[ -z "$(git status --porcelain -- crates)" ] || { echo "crates not restored"; exit 1; }
cmp -s "$RUN_DIR/A.exe" "$RUN_DIR/B.exe" && { echo "A.exe and B.exe are the same file"; exit 1; }
for r in $(seq 1 "${ROUNDS:-2}"); do for arm in A B; do
  o="$RUN_DIR/$arm$r"; mkdir -p "$o"; mapfile -t e < <(sweep_env 1 "$(cygpath -w "$o")")
  "$runs" run "$(cygpath -w "$o")" --max-mem-mb 8192 -- "${e[@]}" "$RUN_DIR/$arm.exe" sweep < /dev/null > "$o/result.txt" 2>&1 || true
  echo "$arm$r $(tail -1 "$o/result.txt")"
done; done | tee "$RUN_DIR/lines.txt"
grep -o '^[AB][0-9]*\|peak[a-z]*=[0-9]*MB' "$RUN_DIR/lines.txt" | paste -sd' ' > "$RUN_DIR/headline.txt"
