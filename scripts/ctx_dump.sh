#!/bin/bash
# ctx_dump.sh <exe> <salts...>: one arm of the streams sweep per salt (`streams_ab.sh`'s `arm()` without arm B, the table check or the
# held-out checks), into $RUN_DIR/s<salt>_A. The exe's <exe>.env sets POOL=4, EXTRAS_SELECT=first, POOL_DUMP=1, so each mine
# also writes dump_<name>_pool.tsv and dump_<name>_served.txt (driver.rs header) and its log carries `RULEMINER label:` lines
# (docs/superpowers/plans/2026-11-01-context-aware-scorer.md, Task 5). Exits 1 if an arm exits non-zero, a mine lacks its
# dump, or a mine that reports stragglers has no label line.
exe=$1; shift
root="$(cd "$(dirname "$0")/.." && pwd)"
runs="$root/tools/runs/target/release/runs.exe"
[ -x "$runs" ] || { echo "ctx_dump: $runs not built (cargo build --release in tools/runs)"; exit 1; }
[ -n "${RUN_DIR:-}" ] || { echo "ctx_dump: RUN_DIR unset (launch through run.ps1)"; exit 1; }
status=0
for s in "$@"; do
  o="$RUN_DIR/s${s}_A"
  mkdir -p "$o"; rm -f "$o/exit"
  "$runs" run "$(cygpath -w "$o")" -- MACHINE_STATE=0 SWEEP=cold:streams "SALT=$s" "SWEEP_OUT=$(cygpath -w "$o")" "$exe" sweep < /dev/null > "$o/result.txt" 2>&1
  echo $? > "$o/exit"
  echo "salt $s: exit $(cat "$o/exit") $(tail -1 "$o/result.txt")"
  [ "$(cat "$o/exit")" = 0 ] || { status=1; continue; }
  for log in "$o"/cold_streams_streams_*_none/mine_*.log; do
    d=$(dirname "$log"); m=$(basename "$log" .log); m=${m#mine_}
    [ -s "$d/dump_${m}_pool.tsv" ] && [ -f "$d/dump_${m}_served.txt" ] || { echo "salt $s: $log has no pool dump"; status=1; }
    if grep -qE '^RULEMINER [1-9][0-9]* stragglers of' "$log" && ! grep -q '^RULEMINER label:' "$log"; then
      echo "salt $s: $log reports stragglers but no label line"; status=1
    fi
  done
done
exit $status
