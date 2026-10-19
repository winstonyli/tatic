# salts_ab.sh <exe A> <exe B> <salts...>: per salt, SWEEP=cold:cmp3d (extras on, 2 lanes, 6 scoring workers) with A and
# B, A first on odd salts and B first on even ones, each a `runs run` (job CPU and wall) into $RUN_DIR/s<salt>_<A|B>;
# a watchdog stops an exe past 8 GB. Then per loop the M of each arm and whether their rules agree, and per arm the
# totals of M, wall and job CPU.
a=$1; b=$2; shift 2
runs="$(dirname "$0")/../../../../tools/runs/target/release/runs.exe"
for s in "$@"; do
  [ $((s % 2)) = 1 ] && order="A B" || order="B A"
  for arm in $order; do
    [ $arm = A ] && exe=$a || exe=$b
    name=$(basename "$exe" | sed 's/\.[Ee][Xx][Ee]$//'); o="$RUN_DIR/s${s}_$arm"; mkdir -p "$o"; rm -f "$o/exit"
    ( "$runs" run "$(cygpath -w "$o")" -- MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=$s "SWEEP_OUT=$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture < /dev/null > "$o/result.txt" 2>&1; echo $? > "$o/exit" ) &
    while [ ! -f "$o/exit" ]; do
      mb=$(powershell -NoProfile -Command "[int]((Get-Process $name -EA 0 | Measure-Object WorkingSet64 -Sum).Sum/1MB)" < /dev/null | tr -d '\r')
      [ "${mb:-0}" -gt 8192 ] && { echo "salt $s $arm: over 8 GB ($mb MB), stopped"; taskkill //F //IM "$name.exe" > /dev/null; }
      ping -n 6 127.0.0.1 > /dev/null
    done
    echo "salt $s $arm: exit $(cat "$o/exit") $(tail -1 "$o/result.txt")"
  done
  for l in 1 2 3; do
    m() { grep "15-$l" "$RUN_DIR/s${s}_$1/cold_cmp3d.tsv" 2>/dev/null | cut -f4; }
    f="cold_cmp3d_cmp3d_${l}_none/rules.txt"
    cmp -s "$RUN_DIR/s${s}_A/$f" "$RUN_DIR/s${s}_B/$f" && same=same || same=differ
    echo "salt $s loop $l: M A $(m A) B $(m B), rules $same"
  done
done
for arm in A B; do
  m=0
  for s in "$@"; do for v in $(cut -f4 "$RUN_DIR/s${s}_$arm/cold_cmp3d.tsv" 2>/dev/null | grep -E '^[0-9]+$'); do m=$((m + v)); done; done
  echo "total $arm: M $m; $(cat "$RUN_DIR"/s*_$arm/result.txt | grep -oE '(wall|jobcpu)=[0-9.]+' | awk -F= '{t[$1]+=$2} END {printf "wall %.0f s, job cpu %.0f s", t["wall"], t["jobcpu"]}')"
done
