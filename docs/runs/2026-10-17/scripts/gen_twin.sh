# gen_twin.sh <exe> <extras root> <salt>...: cold sweeps with MINE_SOURCE=file (patches/extra_file.patch) per arm of $ARMS
# (default "full untwin control"), reading <extras root>/<arm>/s<salt>/<family>_<phase>.txt: full replays the pad arm's
# extras, untwin drops those whose padding-stripped form twins a served law, control drops as many others
# (scripts/pad_files.py). Counts are the pad arm's, so take() keeps every line. Prints as gen_cost.sh does.
exe=$1; root=$2; shift 2
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
for s in "$@"; do
  for arm in ${ARMS:-full untwin control}; do
    o="$d/${arm}_$s"; mkdir -p "$o"; t0=$(date +%s)
    MINE_SOURCE=file MINE_EXTRA=add3:60,sbo3:180,cmp3d:350 MINE_EXTRA_DIR="$(cygpath -w "$root/$arm/s$s")" \
      MACHINE_STATE=0 SALT=$s SWEEP=cold SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1
    echo "$? $(( $(date +%s) - t0 ))" > "$o/exit_secs"
    echo "salt $s $arm: $(awk -F'\t' '{split($5,m,","); t[$1]+=m[2]+m[3]; a+=m[2]+m[3]; r+=$6; c+=$7} END {printf "M %d (cmp3d %d add3 %d sbo3 %d) rules %d loop secs %d", a, t["cmp3d"], t["add3"], t["sbo3"], r, c}' "$o/cold.tsv"), exit+secs $(cat "$o/exit_secs")"
  done
done
