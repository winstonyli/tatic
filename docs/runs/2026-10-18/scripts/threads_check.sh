# threads_check.sh <exe> <salt>: whether the miner's choices depend on its scoring workers. SWEEP=cold:cmp3d (extras on,
# 2 lanes) at LOOP_THREADS=6 and LOOP_THREADS=1, wall seconds per arm, and per loop whether the two arms' rules agree.
# Since each candidate is scored from an empty memo (docs/decisions/2026-10-17-monotone-join.md) every loop should agree.
exe=$1; s=$2
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
for t in 6 1; do
  o="$d/t$t"; mkdir -p "$o"; t0=$(date +%s)
  LOOP_THREADS=$t MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=$s SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1
  echo "threads $t: exit $? wall $(( $(date +%s) - t0 )) s"
done
for r in "$d"/t6/*/rules.txt; do
  l=${r#"$d"/t6/}
  cmp -s "$r" "$d/t1/$l" && echo "$l: same" || echo "$l: DIFFERS"
done
