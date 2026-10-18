# op_cache.sh <exe> <reps> <bits>...: salt 6's cmp3d mine (`SWEEP=mines:cmp3d`) under `OP_CACHE_BITS=<b>` (patches/op_cache.patch:
# a per-thread cache of `Term::op` results in front of the shared table; 0 = off), arms alternated by `runs time`, job CPU and
# wall per run into $RUN_DIR; then each run's join line and Term::op counts, and whether its rules equal the first run's.
exe=$1; reps=$2; shift 2
d=$(cygpath -w "$RUN_DIR"); args=()
for b in "$@"; do args+=(-- "b$b" OP_CACHE_BITS=$b MACHINE_STATE=0 SALT=6 SWEEP=mines:cmp3d "SWEEP_OUT=$d\{arm}_{r}" "$exe" driver::sweep --exact --ignored --nocapture); done
"$(dirname "$0")/../../../../tools/runs/target/release/runs.exe" time "$d" --rounds "$reps" --quiet-secs 0 "${args[@]}"
first=$(ls -d "$RUN_DIR"/b*_* | head -1)
for o in "$RUN_DIR"/b*_*/; do
  m="$o/lib_cmp3d/mine_ref.log"
  echo "$(basename "$o"): $(grep -h 'RULEMINER join:\|OPPROBE' "$m" | tr '\n' ' ') rules $(cmp -s "$o/lib_cmp3d/rules.txt" "$first/lib_cmp3d/rules.txt" && echo same || echo DIFFERENT)"
done
