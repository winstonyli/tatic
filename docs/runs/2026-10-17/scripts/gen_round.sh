# gen_round.sh <exe> <salt>...: cold sweeps per arm of $ARMS (default: off, legacy, the four generator arms, and the matched
# pair m08 and stream_m08), one after another, into kk.sh's directory ($RUN_DIR under run.ps1): <arm>_<salt>/. Arms (the
# law generator's plan, Tasks 6-7): off (ABLATE=gen), plain (no variables, for a build before the generator), f04 and f08
# (fresh slices, GEN_F), s08 and s16 (GEN_SHARED=1), legacy (GEN_COUNTS=legacy, the probe's counts), m08 (f08 with
# GEN_N=matched: n capped at what the filtered stream list fits), stream_<arm> (GEN_SOURCE=stream at that arm's n and
# slices: the stream control; only stream_m08 fits, the filtered stream being 5-20x short of the other arms' n). Prints
# mined-batch M per family, rules and summed loop seconds per arm and salt.
# After the default (2026-10-18): GEN_F, GEN_SHARED and GEN_COUNTS are gone, so f04-s16 and legacy all run as s16, and
# m08 / stream_m08 take shared slices at the stream's fit (a larger n than the measured fresh pair). Reproduce rounds A
# and B on a5da697.
exe=$1; shift
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
arm_env() {
  case $1 in
    plain) ;;
    off) export ABLATE=gen ;;
    f04) export GEN_F=0.04 ;;
    f08) export GEN_F=0.08 ;;
    s08) export GEN_F=0.08 GEN_SHARED=1 ;;
    s16) export GEN_F=0.16 GEN_SHARED=1 ;;
    legacy) export GEN_COUNTS=legacy ;;
    m08) export GEN_F=0.08 GEN_N=matched ;;
    stream_*) arm_env "${1#stream_}" && export GEN_SOURCE=stream ;;
    *) echo "unknown arm $1"; return 1 ;;
  esac
}
for s in "$@"; do
  for arm in ${ARMS:-off legacy f04 f08 s08 s16 m08 stream_m08}; do
    (
      arm_env "$arm" || exit 1
      o="$d/${arm}_$s"; mkdir -p "$o"; t0=$(date +%s)
      MACHINE_STATE=0 SALT=$s SWEEP=cold SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1
      echo "$? $(( $(date +%s) - t0 ))" > "$o/exit_secs"
    )
    o="$d/${arm}_$s"
    echo "salt $s $arm: $(awk -F'\t' '{split($5,m,","); t[$1]+=m[2]+m[3]; a+=m[2]+m[3]; r+=$6; c+=$7} END {printf "M %d (cmp3d %d add3 %d sbo3 %d) rules %d loop secs %d", a, t["cmp3d"], t["add3"], t["sbo3"], r, c}' "$o/cold.tsv"), exit+secs $(cat "$o/exit_secs")"
  done
done
