# store_probe.sh <exe> <salt>...: SWEEP=cold:cmp3d per salt with patches/store_probe.patch (on 8498170), which keeps per thread across rule sets
# every met search's path steps labeled with their laws and, before each non-memo search, looks for a stored path through the
# current laws; prints each salt's summed `RULEMINER join` and `RULEMINER store` (served, within the cap, of them failed,
# summed length, query s, edges) counts.
exe=$1; shift
for s in "$@"; do
  d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")/s$s; mkdir -p "$d"
  t0=$(date +%s)
  MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=$s SWEEP_OUT="$(cygpath -w "$d")" "$exe" driver::sweep --exact --ignored --nocapture > "$d/log.txt" 2>&1
  echo "salt $s: exit $? wall $(( $(date +%s) - t0 )) s"
  for k in join store; do
    grep -h "RULEMINER $k:" "$d"/*/mine_*.log | sed 's/[^0-9.]\+/ /g' | awk -v s=$s -v k=$k '{for (i = 1; i <= NF; i++) t[i] += $i; n = NF} END {printf "salt %s %s", s, k; for (i = 1; i <= n; i++) printf " %d", t[i]; print ""}'
  done
done
