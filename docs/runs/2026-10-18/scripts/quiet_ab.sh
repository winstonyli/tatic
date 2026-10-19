# quiet_ab.sh <salt> <rounds> <exe>...: `runs time` over the exes (SWEEP=cold:cmp3d at 1 lane, each exe an arm named after
# it), arms alternated per round and a round kept only while other load stays under `runs time`'s limit; job CPU and wall
# per run into $RUN_DIR. Then whether each run's files agree with the first's (same_arms.sh).
s=$1; rounds=$2; shift 2
here=$(dirname "$0"); d=$(cygpath -w "$RUN_DIR"); args=()
for exe in "$@"; do
  name=$(basename "$exe" | sed 's/\.[Ee][Xx][Ee]$//')
  args+=(-- "$name" SWEEP=cold:cmp3d MACHINE_STATE=0 SALT=$s SWEEP_LANES=1 "SWEEP_OUT=$d\{arm}_{r}" "$exe" driver::sweep --exact --ignored --nocapture)
done
"$here/../../../../tools/runs/target/release/runs.exe" time "$d" --rounds "$rounds" --max-hours 3 "${args[@]}" < /dev/null
first=$(ls -d "$RUN_DIR"/*_*/ | head -1)
for o in "$RUN_DIR"/*_*/; do
  [ "$o" = "$first" ] || echo "$(basename "$o") vs $(basename "$first"): $(bash "$here/../../2026-10-17/scripts/same_arms.sh" "$first" "$o" | tr '\n' ' ')"
done
