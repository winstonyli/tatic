# threads_check.sh <exe> <salt>: whether the miner's choices depend on its scoring workers. SWEEP=cold:cmp3d (extras on,
# 2 lanes) at LOOP_THREADS=6 and LOOP_THREADS=1, wall seconds per arm, and per loop whether the two arms' rules agree.
# Since each candidate is scored from an empty memo (docs/decisions/2026-10-17-monotone-join.md) every loop should agree.
# Last line: loops that agree, and arms that failed (non-zero exit or no rules); exits 1 unless all agree and none failed.
exe=$1; s=$2
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
failed=0
for t in 6 1; do
  o="$d/t$t"; mkdir -p "$o"; t0=$(date +%s)
  LOOP_THREADS=$t MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=$s SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1
  e=$?
  echo "threads $t: exit $e wall $(( $(date +%s) - t0 )) s"
  [ $e = 0 ] && compgen -G "$o/*/rules.txt" > /dev/null || failed=$((failed + 1))
done
same=0; loops=0
for r in "$d"/t6/*/rules.txt; do
  [ -f "$r" ] || continue
  l=${r#"$d"/t6/}; loops=$((loops + 1))
  cmp -s "$r" "$d/t1/$l" && { echo "$l: same"; same=$((same + 1)); } || echo "$l: DIFFERS"
done
echo "threads_check: rules same in $same of $loops loops; $failed of 2 arms failed"
[ $failed = 0 ] && [ $same = $loops ]
