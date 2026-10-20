# inner_probe.sh <exe> <salt>...: SWEEP=cold:cmp3d per salt with patches/inner_probe.patch, which reruns every join
# search without the inner-first skip and compares; prints each salt's summed `RULEMINER inprobe` counts (fields in the
# patch's JoinCost.probe comment).
exe=$1; shift
for s in "$@"; do
  d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")/s$s; mkdir -p "$d"
  t0=$(date +%s)
  MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=$s SWEEP_OUT="$(cygpath -w "$d")" "$exe" driver::sweep --exact --ignored --nocapture > "$d/log.txt" 2>&1
  echo "salt $s: exit $? wall $(( $(date +%s) - t0 )) s"
  grep -h "RULEMINER inprobe" "$d"/*/mine_*.log | tr -d '[],' | awk -v s=$s '{for (i = 3; i <= NF; i++) t[i] += $i} END {printf "salt %s sum", s; for (i = 3; i <= NF; i++) printf " %d", t[i]; print ""}'
done
