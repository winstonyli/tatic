# class_probe.sh <exe> <salt>...: SWEEP=cold:cmp3d per salt with patches/class_probe.patch (on 15cb302), which keeps per thread and
# rule set the classes of terms proven equal by met searches' paths and the terms searches reached; prints each salt's summed
# `RULEMINER join` (searches reached met hits) and `RULEMINER probe` (both sides in one class, of them met, a side in a class,
# reached terms reached before, reached terms) counts.
exe=$1; shift
for s in "$@"; do
  d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")/s$s; mkdir -p "$d"
  t0=$(date +%s)
  MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=$s SWEEP_OUT="$(cygpath -w "$d")" "$exe" driver::sweep --exact --ignored --nocapture > "$d/log.txt" 2>&1
  echo "salt $s: exit $? wall $(( $(date +%s) - t0 )) s"
  for k in join probe; do
    grep -h "RULEMINER $k:" "$d"/*/mine_*.log | sed 's/[^0-9.]\+/ /g' | awk -v s=$s -v k=$k '{for (i = 1; i <= NF; i++) t[i] += $i; n = NF} END {printf "salt %s %s", s, k; for (i = 1; i <= n; i++) printf " %d", t[i]; print ""}'
  done
done
