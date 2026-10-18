# join_paths.sh <exe> <salt>: SWEEP=cold:cmp3d (extras on, 2 lanes) with patches/join_paths.patch's JOIN_PATHS log (one
# line per met search: steps on side a, on side b, uphill steps on each, peak size over the larger side, sizes of a and
# b, each side's size changes root first), then the summary: uphill steps per path, and on paths with a side 5 or more
# deep, the deep side's uphill steps.
exe=$1; s=$2
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
t0=$(date +%s)
JOIN_PATHS="$(cygpath -w "$d")\\paths" MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=$s SWEEP_OUT="$(cygpath -w "$d")" "$exe" driver::sweep --exact --ignored --nocapture > "$d/log.txt" 2>&1
echo "exit $? wall $(( $(date +%s) - t0 )) s"
cat "$d"/paths.* | awk -F'\t' '
  { n++; u = $3 + $4; tot[u > 8 ? 9 : u]++; pk[$5 > 2 ? 3 : $5]++
    deep = ($1 >= $2) ? 1 : 2; dd = $deep; du = $(deep + 2)
    if (dd >= 5) { nd++; dup[du > 4 ? 5 : du]++ } }
  END {
    printf "met paths %d\nuphill steps per path:", n; for (i = 0; i <= 9; i++) printf " %s%d:%d", (i == 9 ? ">" : ""), (i == 9 ? 8 : i), tot[i]; print ""
    printf "peak over the larger side:"; for (i = -9; i <= 3; i++) if (i in pk) printf " %s%d:%d", (i == 3 ? ">=" : ""), i, pk[i]; print ""
    printf "paths with a side >= 5 deep %d; uphill steps on that side:", nd; for (i = 0; i <= 5; i++) printf " %s%d:%d", (i == 5 ? ">=" : ""), i, dup[i]; print ""
  }'
