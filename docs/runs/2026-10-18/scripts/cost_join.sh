# cost_join.sh <exe> <salt>: SWEEP=cold:cmp3d (extras on, 2 lanes) once per budget in BUDGETS (default "3 4") with
# patches/cost_join.patch's shadow search (JOIN_SHADOW) on the pairs clearing JOIN_SAMPLE_MASK (default 7), then per
# budget: the shadow's outcome against the real join's, and terms reached per search (p50, p99, max) for each.
exe=$1; s=$2
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
for b in ${BUDGETS:-3 4}; do
  o="$d/b$b"; mkdir -p "$o"; t0=$(date +%s)
  JOIN_BUDGET=$b JOIN_SHADOW="$(cygpath -w "$o")\\shadow" MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=$s SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1
  echo "budget $b: exit $? wall $(( $(date +%s) - t0 )) s"
  cat "$o"/shadow.* | awk -F'\t' '{ k = ($1 ? "met" : "fail") "->" $3; n[k]++ } END { for (k in n) printf "  real %s: %d\n", k, n[k] }' | sort
  for col in 2 4; do
    printf "  %s reached: " $([ $col = 2 ] && echo real || echo shadow)
    cat "$o"/shadow.* | cut -f$col | sort -n | awk '{ v[NR] = $1 } END { printf "p50 %d p99 %d p99.9 %d max %d (n %d)\n", v[int(NR * .5)], v[int(NR * .99)], v[int(NR * .999)], v[NR], NR }'
  done
  cat "$o"/shadow.* | awk -F'\t' '$3 == "fail" { f[$1]++; r[$1] += $4 } END { for (k in f) printf "  shadow fail on real %s: mean reached %.0f\n", (k ? "met" : "fail"), r[k] / f[k] }'
done
