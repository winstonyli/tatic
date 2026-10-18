# interner_ab.sh <exe A> <exe B> <salt>: SWEEP=cold:cmp3d at 1 lane, in the order A B B A (drift falls on both arms
# alike), into kk.sh's directory ($RUN_DIR under run.ps1). Prints each sweep's wall seconds and whether each arm's
# sweeps agree with A's first (same_arms.sh).
a=$1; b=$2; s=$3
here=$(dirname "$0")
d=$(bash "$here/../../2026-10-12/scripts/kk.sh")
i=0
for arm in A B B A; do
  i=$((i + 1))
  [ $arm = A ] && exe=$a || exe=$b
  o="$d/${arm}_$i"; mkdir -p "$o"; t0=$(date +%s)
  SWEEP=cold:cmp3d MACHINE_STATE=0 SALT=$s SWEEP_LANES=1 SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1
  echo "$arm $i: exit $? wall $(( $(date +%s) - t0 )) s"
done
for o in B_2 B_3 A_4; do
  echo "$o vs A_1: $(bash "$here/../../2026-10-17/scripts/same_arms.sh" "$d/A_1" "$d/$o" | tr '\n' ' ')"
done
