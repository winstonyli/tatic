# serve_bound_ab.sh <exe> <salts...>: per salt, SWEEP=cold:cmp3d (extras on, 2 lanes) as built and with
# JOIN_COST_BOUND=4 (patches/cost_search.patch: serving's join bounded by 4 size-increasing steps, the miner's as built),
# then per loop: M of each arm and whether their rules agree. A watchdog stops the exe past 12 GB in all.
exe=$1; shift
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
name=$(basename "$exe" | sed 's/\.[Ee][Xx][Ee]$//')
for s in "$@"; do
  for arm in real bound; do
    o="$d/s${s}_$arm"; mkdir -p "$o"; t0=$(date +%s)
    ( [ $arm = bound ] && export JOIN_COST_BOUND=4
      MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=$s SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1; echo $? > "$o/exit" ) &
    while [ ! -f "$o/exit" ]; do
      mb=$(powershell -NoProfile -Command "[int]((Get-Process $name -EA 0 | Measure-Object WorkingSet64 -Sum).Sum/1MB)" | tr -d '\r')
      [ "${mb:-0}" -gt 12288 ] && { echo "salt $s $arm: over 12 GB ($mb MB), stopped"; taskkill //F //IM "$name.exe" > /dev/null; }
      ping -n 4 127.0.0.1 > /dev/null
    done
    echo "salt $s $arm: exit $(cat "$o/exit") wall $(( $(date +%s) - t0 )) s"
  done
  for l in 1 2 3; do
    r="$d/s${s}_real/cold_cmp3d_cmp3d_${l}_none"; b="$d/s${s}_bound/cold_cmp3d_cmp3d_${l}_none"
    same=$(cmp -s "$r/rules.txt" "$b/rules.txt" && echo same || echo differ)
    echo "salt $s loop $l: M real $(grep "15-$l" "$d/s${s}_real/cold_cmp3d.tsv" | cut -f4) bound $(grep "15-$l" "$d/s${s}_bound/cold_cmp3d.tsv" | cut -f4), rules $same"
  done
done
