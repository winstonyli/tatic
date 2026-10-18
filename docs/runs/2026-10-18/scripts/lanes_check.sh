# lanes_check.sh <exe> <salt>: one sweep per lane count in LANES (default "1 2"), per arm in ARMS (default "all cold"), into
# kk.sh's directory ($RUN_DIR under run.ps1): `all` (the default SWEEP, mines own cold, with ABLATE=gen) and `cold`
# (SWEEP=cold, extras on). Prints each sweep's wall seconds and whether the arm's first two sweeps agree (same_arms.sh:
# every stage's .tsv but its seconds, every rules.txt). LANES="1 1" checks that a sweep repeats.
exe=$1; s=$2
here=$(dirname "$0")
d=$(bash "$here/../../2026-10-12/scripts/kk.sh")
for arm in ${ARMS:-all cold}; do
  i=0
  for lanes in ${LANES:-1 2}; do
    i=$((i + 1))
    (
      [ $arm = all ] && export ABLATE=gen || export SWEEP=cold
      o="$d/${arm}_$i"; mkdir -p "$o"; t0=$(date +%s)
      MACHINE_STATE=0 SALT=$s SWEEP_LANES=$lanes SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1
      echo "$arm $i, lanes $lanes: exit $? wall $(( $(date +%s) - t0 )) s"
    )
  done
  echo "$arm: $(bash "$here/../../2026-10-17/scripts/same_arms.sh" "$d/${arm}_1" "$d/${arm}_2" | tr '\n' ' ')"
done
