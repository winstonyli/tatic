# hit_probe.sh <exe> <salt>...: SWEEP=cold:cmp3d per salt with patches/hit_probe.patch (on e8bac31): each memo join hit counted by
# met or failed and by the miner's main thread (feeds the join store) or a worker (reads its frozen copy), and whether the
# thread's store would serve the pair. Prints each salt's summed `RULEMINER join`, `store` and `memohits` (met main, met worker,
# failed main, failed worker, then the same four counted only where the store serves the pair).
exe=$1; shift
for s in "$@"; do
  d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")/s$s; mkdir -p "$d"
  t0=$(date +%s)
  MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=$s SWEEP_OUT="$(cygpath -w "$d")" "$exe" driver::sweep --exact --ignored --nocapture > "$d/log.txt" 2>&1
  echo "salt $s: exit $? wall $(( $(date +%s) - t0 )) s"
  for k in join "join store" memohits; do
    grep -h "RULEMINER $k:" "$d"/*/mine_*.log | sed 's/[^0-9.]\+/ /g' | awk -v s=$s -v k="$k" '{for (i = 1; i <= NF; i++) t[i] += $i; n = NF} END {printf "salt %s %s", s, k; for (i = 1; i <= n; i++) printf " %d", t[i]; print ""}'
  done
done
