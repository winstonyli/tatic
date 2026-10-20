# quiet_ab.sh <salt> <rounds> <exe>...: `runs time` over the exes (SWEEP=cold:cmp3d at 1 lane, each exe an arm named after
# it, `_<k>` added to the k-th repeat of a name, so an exe given twice is an A/A), arms alternated per round and a round
# kept only while other load stays under `runs time`'s limit; job CPU and wall per run into $RUN_DIR. `QUIET_AB_FLAGS`
# adds flags to `runs time` (`--quiet-secs 10`, say). Then whether each run's files agree with the first's (same_arms.sh).
s=$1; rounds=$2; shift 2
here=$(dirname "$0"); d=$(cygpath -w "$RUN_DIR"); args=(); declare -A seen
for exe in "$@"; do
  name=$(basename "$exe" | sed 's/\.[Ee][Xx][Ee]$//')
  seen[$name]=$(( ${seen[$name]:-0} + 1 )); [ "${seen[$name]}" = 1 ] || name="${name}_${seen[$name]}"
  args+=(-- "$name" SWEEP=cold:cmp3d MACHINE_STATE=0 SALT=$s SWEEP_LANES=1 "SWEEP_OUT=$d\{arm}_{r}" "$exe" driver::sweep --exact --ignored --nocapture)
done
"$here/../../../../tools/runs/target/release/runs.exe" time "$d" --rounds "$rounds" --max-hours 3 $QUIET_AB_FLAGS "${args[@]}" < /dev/null
first=$(ls -d "$RUN_DIR"/*_*/ | head -1)
for o in "$RUN_DIR"/*_*/; do
  [ "$o" = "$first" ] || echo "$(basename "$o") vs $(basename "$first"): $(bash "$here/../../2026-10-17/scripts/same_arms.sh" "$first" "$o" | tr '\n' ' ')"
done
bash "$here/../../2026-10-20/scripts/join_work.sh" "$RUN_DIR"/*_*/
