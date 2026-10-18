# gen_src.sh <exe> <salt>...: cold sweeps with no extras (plain) and with MINE_EXTRA=add3:60,sbo3:180,cmp3d:350 from each
# source (MINE_SOURCE=stream|grammar, driver::extra_laws), one after another, into kk.sh's directory ($RUN_DIR under run.ps1):
# <arm>_<salt>/ holds cold.tsv, the log and its exit code and wall seconds. Prints mined-batch M (the two batches served after
# a mine: cold.tsv column 5's second and third entries) per family and arm.
exe=$1; shift
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
for s in "$@"; do
  for arm in plain stream grammar; do
    (
      o="$d/${arm}_$s"; mkdir -p "$o"; t0=$(date +%s)
      [ $arm = plain ] || export MINE_EXTRA=add3:60,sbo3:180,cmp3d:350 MINE_SOURCE=$arm
      MACHINE_STATE=0 SALT=$s SWEEP=cold SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1
      echo "$? $(( $(date +%s) - t0 ))" > "$o/exit_secs"
    )
    o="$d/${arm}_$s"
    echo "salt $s $arm: $(awk -F'\t' '{split($5,m,","); t[$1]+=m[2]+m[3]; a+=m[2]+m[3]} END {printf "M %d (cmp3d %d add3 %d sbo3 %d)", a, t["cmp3d"], t["add3"], t["sbo3"]}' "$o/cold.tsv"), exit+secs $(cat "$o/exit_secs")"
  done
done
