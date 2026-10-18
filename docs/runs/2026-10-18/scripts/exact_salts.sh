# exact_salts.sh <exe> <salts...>: the cost of the exact join memo over salts (patches/join_exact.patch). Per salt,
# SWEEP=cold:cmp3d (extras on, 2 lanes) as built (base) and with JOIN_EXACT=1 (exact), both at the default 6 miner
# threads; wall seconds per arm, per loop M of each arm and whether their rules agree, then totals over the salts.
# A watchdog stops the exe past 12 GB in all.
exe=$1; shift
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
name=$(basename "$exe" | sed 's/\.[Ee][Xx][Ee]$//')
for s in "$@"; do
  for arm in base exact; do
    o="$d/s${s}_$arm"; mkdir -p "$o"; rm -f "$o/exit"; t0=$(date +%s)
    ( [ $arm = exact ] && export JOIN_EXACT=1
      MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=$s SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1; echo $? > "$o/exit" ) &
    while [ ! -f "$o/exit" ]; do
      mb=$(powershell -NoProfile -Command "[int]((Get-Process $name -EA 0 | Measure-Object WorkingSet64 -Sum).Sum/1MB)" | tr -d '\r')
      [ "${mb:-0}" -gt 12288 ] && { echo "salt $s $arm: over 12 GB ($mb MB), stopped"; taskkill //F //IM "$name.exe" > /dev/null; }
      ping -n 4 127.0.0.1 > /dev/null
    done
    w=$(( $(date +%s) - t0 )); echo "$w" > "$o/wall"
    echo "salt $s $arm: exit $(cat "$o/exit") wall $w s"
  done
  for l in 1 2 3; do
    r="$d/s${s}_base/cold_cmp3d_cmp3d_${l}_none"; x="$d/s${s}_exact/cold_cmp3d_cmp3d_${l}_none"
    same=$(cmp -s "$r/rules.txt" "$x/rules.txt" && echo same || echo differ)
    echo "salt $s loop $l: M base $(grep "15-$l" "$d/s${s}_base/cold_cmp3d.tsv" | cut -f4) exact $(grep "15-$l" "$d/s${s}_exact/cold_cmp3d.tsv" | cut -f4), rules $same"
  done
done
for arm in base exact; do
  m=0; w=0
  for s in "$@"; do
    w=$(( w + $(cat "$d/s${s}_$arm/wall") ))
    for v in $(cut -f4 "$d/s${s}_$arm/cold_cmp3d.tsv" | grep -E '^[0-9]+$'); do m=$(( m + v )); done
  done
  echo "total $arm: M $m wall $w s"
done
