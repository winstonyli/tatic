# join_exact.sh <exe> <salt>: whether the miner's choices depend on its memo's history. SWEEP=cold:cmp3d (extras on, 2 lanes)
# four ways (patches/join_exact.patch): base6 (as built), base1 (LOOP_THREADS=1: one scoring worker, so another memo history),
# exact6 and exact1 (JOIN_EXACT=1: a met join's trace is every term it examined). Wall seconds per arm, and per loop whether
# base1 agrees with base6 and exact1 with exact6 (an exact memo makes the thread count invisible), and exact6 with base6.
exe=$1; s=$2
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
for arm in base6 base1 exact6 exact1; do
  (
    case $arm in exact*) export JOIN_EXACT=1;; esac
    export LOOP_THREADS=${arm: -1}
    o="$d/$arm"; mkdir -p "$o"; t0=$(date +%s)
    MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=$s SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1
    echo "$arm: exit $? wall $(( $(date +%s) - t0 )) s"
  )
done
for r in "$d"/base6/*/rules.txt; do
  l=${r#"$d"/base6/}
  same() { cmp -s "$d/$1/$l" "$d/$2/$l" && echo same || echo differs; }
  echo "$l: base1 $(same base6 base1), exact1 $(same exact6 exact1), exact6 vs base6 $(same base6 exact6)"
done
