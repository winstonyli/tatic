# snap_salts.sh <exe> <salts...>: the memo without history across candidates (patches/memo_per_cand.patch). Per salt,
# SWEEP=cold:cmp3d (extras on, 2 lanes) in each arm of ARMS (default "base6 snap6 snap1": as built, MEMO_PER_CAND=1, at
# LOOP_THREADS 6 or 1); wall seconds per arm, per loop M of each arm, whether snap6's rules equal base6's and snap1's
# equal snap6's (an arm missing reads "-"), then M and wall totals per arm. A watchdog stops the exe past 8 GB in all.
exe=$1; shift
arms=${ARMS:-base6 snap6 snap1}
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
name=$(basename "$exe" | sed 's/\.[Ee][Xx][Ee]$//')
for s in "$@"; do
  for arm in $arms; do
    o="$d/s${s}_$arm"; mkdir -p "$o"; rm -f "$o/exit"; t0=$(date +%s)
    ( case $arm in snap*) export MEMO_PER_CAND=1;; esac
      export LOOP_THREADS=${arm: -1}
      MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=$s SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1; echo $? > "$o/exit" ) &
    while [ ! -f "$o/exit" ]; do
      mb=$(powershell -NoProfile -Command "[int]((Get-Process $name -EA 0 | Measure-Object WorkingSet64 -Sum).Sum/1MB)" | tr -d '\r')
      [ "${mb:-0}" -gt 8192 ] && { echo "salt $s $arm: over 8 GB ($mb MB), stopped"; taskkill //F //IM "$name.exe" > /dev/null; }
      ping -n 4 127.0.0.1 > /dev/null
    done
    w=$(( $(date +%s) - t0 )); echo "$w" > "$o/wall"
    echo "salt $s $arm: exit $(cat "$o/exit") wall $w s"
  done
  for l in 1 2 3; do
    m() { [ -f "$d/s${s}_$1/cold_cmp3d.tsv" ] && grep "15-$l" "$d/s${s}_$1/cold_cmp3d.tsv" | cut -f4 || echo -; }
    same() { f="cold_cmp3d_cmp3d_${l}_none/rules.txt"; [ -f "$d/s${s}_$1/$f" ] && [ -f "$d/s${s}_$2/$f" ] || { echo -; return; }; cmp -s "$d/s${s}_$1/$f" "$d/s${s}_$2/$f" && echo same || echo differ; }
    echo "salt $s loop $l: M base6 $(m base6) snap6 $(m snap6) snap1 $(m snap1); snap6 vs base6 $(same base6 snap6), snap1 vs snap6 $(same snap6 snap1)"
  done
done
for arm in $arms; do
  m=0; w=0
  for s in "$@"; do
    w=$(( w + $(cat "$d/s${s}_$arm/wall") ))
    for v in $(cut -f4 "$d/s${s}_$arm/cold_cmp3d.tsv" | grep -E '^[0-9]+$'); do m=$(( m + v )); done
  done
  echo "total $arm: M $m wall $w s"
done
