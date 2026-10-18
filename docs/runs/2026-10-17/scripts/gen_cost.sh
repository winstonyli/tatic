# gen_cost.sh <exe> <salt>...: cold sweeps per arm of $ARMS (default "half quarter pad nopad"), one after another, into
# kk.sh's directory ($RUN_DIR under run.ps1): <arm>_<salt>/ as in gen_src.sh. Arms: plain (no extras); stream and grammar
# (MINE_SOURCE, gen_src.sh's counts MINE_EXTRA=add3:60,sbo3:180,cmp3d:350); half and quarter (grammar at half and a quarter
# of those counts: matched rules or mining time against stream); pad and nopad (grammar at those counts with only padded laws
# or none, GEN_PAD). Prints mined-batch M per family, rules and summed loop seconds per arm and salt.
exe=$1; shift
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
for s in "$@"; do
  for arm in ${ARMS:-half quarter pad nopad}; do
    (
      full=add3:60,sbo3:180,cmp3d:350
      case $arm in
        plain) ;;
        stream) export MINE_SOURCE=stream MINE_EXTRA=$full ;;
        grammar) export MINE_SOURCE=grammar MINE_EXTRA=$full ;;
        half) export MINE_SOURCE=grammar MINE_EXTRA=add3:30,sbo3:90,cmp3d:175 ;;
        quarter) export MINE_SOURCE=grammar MINE_EXTRA=add3:15,sbo3:45,cmp3d:88 ;;
        pad|nopad) export MINE_SOURCE=grammar MINE_EXTRA=$full GEN_PAD=$arm ;;
        *) echo "unknown arm $arm"; exit 1 ;;
      esac
      o="$d/${arm}_$s"; mkdir -p "$o"; t0=$(date +%s)
      MACHINE_STATE=0 SALT=$s SWEEP=cold SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1
      echo "$? $(( $(date +%s) - t0 ))" > "$o/exit_secs"
    )
    o="$d/${arm}_$s"
    echo "salt $s $arm: $(awk -F'\t' '{split($5,m,","); t[$1]+=m[2]+m[3]; a+=m[2]+m[3]; r+=$6; c+=$7} END {printf "M %d (cmp3d %d add3 %d sbo3 %d) rules %d loop secs %d", a, t["cmp3d"], t["add3"], t["sbo3"], r, c}' "$o/cold.tsv"), exit+secs $(cat "$o/exit_secs")"
  done
done
