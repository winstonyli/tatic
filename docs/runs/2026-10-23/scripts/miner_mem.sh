#!/bin/bash
# miner_mem.sh <exe>: where a sweep worker's ~500 MB peak comes from (docs/tier-cycle.md, "One screen memo and candidate
# index per process", what the rest of that peak is). One SWEEP=cold:cmp3d sweep at salt 1, as salts_ab.sh runs an arm.
# The exe is d97d418 plus one of patches/miner_*.patch. miner_mem.patch: the global allocator counts live bytes
# (mimalloc underneath), and each `rule_miner` phase prints live MB, the live peak since the previous phase, and the
# process's commit and peak commit. On top of it: miner_mem_collect (the commit after mi_collect(true)), miner_stack
# (each miner thread's committed stack as it exits), miner_seg4 (CHECK_SEGMENT 4 MB), miner_ws (working set). Run
# miner-mem-purge0 used the miner_mem exe with MIMALLOC_PURGE_DELAY=0 in the environment.
EXE=$1; T="${RUN_DIR:-$TEMP}/miner_mem"; mkdir -p "$T"
runs="$(dirname "$0")/../../../../tools/runs/target/release/runs.exe"
"$runs" run "$(cygpath -w "$T")" -- MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=1 "SWEEP_OUT=$(cygpath -w "$T")" "$EXE" driver::sweep \
  --exact --ignored --nocapture < /dev/null > "$T/result.txt" 2>&1; rc=$?
echo "sweep exit $rc: $(tail -1 "$T/result.txt")"
grep -rl "RULEMINER mem" "$T" | sort | while read -r f; do
  echo "== ${f#$T/}"; grep -E "RULEMINER (mem|time)|applicable candidates|provable candidates|stragglers of" "$f" | cut -c1-200
done
