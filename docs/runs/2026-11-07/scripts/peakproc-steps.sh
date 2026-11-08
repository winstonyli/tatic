# peakproc-steps.sh: why one exe's gate peakproc takes 256/512 MB steps between runs (k4). Runs the gate's sweep (salt 2)
# of w1's a.exe sequentially under runs.exe, 3 times as the gate runs it and 3 times with mimalloc's purge on, with
# MIMALLOC_SHOW_STATS=1 so each process (sweep parent and its workers) prints its own committed peak at exit. Output in
# $RUN_DIR/<variant>_<i>/. Launch through run.ps1 (-Affinity CFF).
set -u
exe="$LOCALAPPDATA/claude-runs/tatic/w1-exes/a.exe"
runs="$(dirname "$0")/../../../../tools/runs/target/release/runs.exe"
for v in default purge; do
  for i in 1 2 3; do
    o="$RUN_DIR/${v}_$i"; mkdir -p "$o"
    e=(MACHINE_STATE=0 SALT=2 "SWEEP_OUT=$(cygpath -w "$o")" MIMALLOC_SHOW_STATS=1)
    [ $v = purge ] && e+=(MIMALLOC_PURGE_DELAY=0)
    "$runs" run "$(cygpath -w "$o")" --max-mem-mb 8192 -- "${e[@]}" "$exe" sweep < /dev/null > "$o/result.txt" 2>&1
    echo "$v $i: $(tail -1 "$o/result.txt")"
  done
done
grep -ho 'peakproc=[0-9]*' "$RUN_DIR"/*_?/result.txt | tr '\n' ' ' > "$RUN_DIR/headline.txt"
