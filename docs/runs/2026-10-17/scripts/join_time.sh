# join_time.sh <exe> <salt> <reps>: the cmp3d ref mine (`SWEEP=mines:cmp3d`) of a build carrying patches/no_bound.patch,
# with the gain bound on and off (`RULEMINER_NO_BOUND=1`), one run at a time, the arms' order alternating. Into kk.sh's
# directory ($RUN_DIR under run.ps1): <arm>_<rep>/ holds the sweep's files; prints per run the wall seconds, bash
# `times` for the children (it reads 0 here: Git Bash does not see a native child's CPU; use `runs run` for job CPU),
# the mine's join line, rule-set evaluation time and the bound's scorings, and whether the rules mined equal the first run's.
exe=$1; s=$2; reps=$3
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
for rep in $(seq 1 "$reps"); do
  arms="bound none"; [ $((rep % 2)) = 0 ] && arms="none bound"
  for arm in $arms; do
    o="$d/${arm}_$rep"; mkdir -p "$o"
    cpu=$( ( [ $arm = none ] && export RULEMINER_NO_BOUND=1
             t0=$(date +%s.%N)
             MACHINE_STATE=0 SALT=$s SWEEP=mines:cmp3d SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1 < /dev/null
             echo "exit $? wall $(awk -v a="$t0" -v b="$(date +%s.%N)" 'BEGIN {printf "%.1f", b - a}')"; times | tail -1 ) | tr '\n' ' ')
    m="$o/lib_cmp3d/mine_ref.log"
    same=$(cmp -s "$o/lib_cmp3d/rules.txt" "$d/$(ls "$d" | head -1)/lib_cmp3d/rules.txt" && echo same || echo DIFFERENT)
    echo "$arm $rep: $cpu| $(grep -h 'RULEMINER join:\|evaluations:\|gain bound skipped' "$m" | tr '\n' ' ')| rules $same"
  done
done
