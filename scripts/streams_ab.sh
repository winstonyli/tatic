#!/bin/bash
# streams_ab.sh <exe A> <exe B> <salts...>: the gate on the streams (spec §9). Per salt, SWEEP=cold:streams (extras
# on, 2 lanes, 6 scoring workers) with A and B, A first on odd salts and B first on even ones, each a `runs run` (job
# CPU and wall) into $RUN_DIR/s<salt>_<A|B>; a watchdog stops an arm past 8 GB (its own process tree, `tree_mem.ps1`). Then per loop the held-out M under the
# loop's final rules (tests/church_bv/held_{11,13}.txt, CHECK_FAST: the laws that still need a whole-term machine
# proof). Per salt: M, held-out M and job CPU of each arm, and whether each loop's rules agree; per arm the totals, the
# lookup memo's peak (CLASS_MEMO) and the largest peakproc. Last line: loops with the same rules, and arms that failed
# (non-zero exit or no M); exits 1 if any arm failed. Differing rules are reported, not failed.
a=$1; b=$2; shift 2
root="$(cd "$(dirname "$0")/.." && pwd)"
runs="$root/tools/runs/target/release/runs.exe"
[ -x "$runs" ] || { echo "streams_ab: $runs not built (cargo build --release in tools/runs)"; exit 1; }
failed=0; same_n=0; loops=0
held() { # <exe> <rules file>: held-out M over both bands
  local m=0 band line p f n
  for band in 11 13; do
    line=$(MACHINE_STATE=0 CHECK_FAST=1 CHECK_FAMILY=streams CHECK_RULES="$(cygpath -w "$2")" CHECK_LAWFILE="$(cygpath -w "$root/tests/church_bv/held_$band.txt")" "$1" search::rule_set_kernel_check --exact --ignored --nocapture < /dev/null 2>&1 | grep '^CHECKED ')
    p=$(echo "$line" | sed -E 's/^CHECKED ([0-9]+) .*/\1/'); f=$(echo "$line" | sed -E 's/.*\(([0-9]+) with.*/\1/'); n=$(echo "$line" | sed -E 's/.*\), ([0-9]+) not proved.*/\1/')
    [ -n "$line" ] || { echo "held: no CHECKED line for $2 band $band" >&2; echo x; return; }
    m=$((m + p - f + n))
  done
  echo $m
}
for s in "$@"; do
  [ $((s % 2)) = 1 ] && order="A B" || order="B A"
  for arm in $order; do
    [ $arm = A ] && exe=$a || exe=$b
    o="$RUN_DIR/s${s}_$arm"; mkdir -p "$o"; rm -f "$o/exit"
    ( "$runs" run "$(cygpath -w "$o")" -- MACHINE_STATE=0 SWEEP=cold:streams SALT=$s "SWEEP_OUT=$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture < /dev/null > "$o/result.txt" 2>&1; echo $? > "$o/exit" ) &
    while [ ! -f "$o/exit" ]; do
      mb=$(powershell -NoProfile -File "$(cygpath -w "$root/scripts/tree_mem.ps1")" -Match "$(cygpath -w "$o")" < /dev/null | tr -d '\r')
      [ "${mb:-0}" -gt 8192 ] && { echo "salt $s $arm: over 8 GB ($mb MB), stopped"; powershell -NoProfile -File "$(cygpath -w "$root/scripts/tree_mem.ps1")" -Match "$(cygpath -w "$o")" -Kill < /dev/null > /dev/null; }
      ping -n 6 127.0.0.1 > /dev/null
    done
    echo "salt $s $arm: exit $(cat "$o/exit") $(tail -1 "$o/result.txt")"
    [ "$(cat "$o/exit")" = 0 ] && cut -f4 "$o/cold_streams.tsv" 2>/dev/null | grep -qE '^[0-9]+$' || failed=$((failed + 1))
    h=0
    for l in 1 2 3; do v=$(held "$exe" "$o/cold_streams_streams_${l}_none/rules.txt"); [ "$v" = x ] && failed=$((failed + 1)) || h=$((h + v)); done
    echo $h > "$o/held.txt"
  done
  for l in 1 2 3; do
    f="cold_streams_streams_${l}_none/rules.txt"
    cmp -s "$RUN_DIR/s${s}_A/$f" "$RUN_DIR/s${s}_B/$f" && same_n=$((same_n + 1)) || echo "salt $s loop $l: rules differ"
    loops=$((loops + 1))
  done
  m() { cut -f4 "$RUN_DIR/s${s}_$1/cold_streams.tsv" 2>/dev/null | grep -E '^[0-9]+$' | awk '{s += $1} END {print s + 0}'; }
  c() { grep -oE 'jobcpu=[0-9.]+' "$RUN_DIR/s${s}_$1/result.txt" | cut -d= -f2; }
  echo "salt $s: M A $(m A) B $(m B); held A $(cat "$RUN_DIR/s${s}_A/held.txt") B $(cat "$RUN_DIR/s${s}_B/held.txt"); jobcpu A $(c A) B $(c B)"
done
for arm in A B; do
  m=0; h=0
  for s in "$@"; do
    for v in $(cut -f4 "$RUN_DIR/s${s}_$arm/cold_streams.tsv" 2>/dev/null | grep -E '^[0-9]+$'); do m=$((m + v)); done
    h=$((h + $(cat "$RUN_DIR/s${s}_$arm/held.txt" 2>/dev/null || echo 0)))
  done
  memo=$(grep -rh '^CLASS_MEMO' "$RUN_DIR"/s*_$arm 2>/dev/null | awk '{if ($2 > x) x = $2} END {print x + 0}')
  peak=$(grep -h -oE 'peakproc=[0-9]+' "$RUN_DIR"/s*_$arm/result.txt 2>/dev/null | cut -d= -f2 | sort -n | tail -1)
  echo "total $arm: M $m; held $h; $(cat "$RUN_DIR"/s*_$arm/result.txt | grep -oE '(wall|jobcpu)=[0-9.]+' | awk -F= '{t[$1]+=$2} END {printf "wall %.0f s, job cpu %.0f s", t["wall"], t["jobcpu"]}'); memo peak $memo terms; peakproc max $peak"
done
echo "streams_ab: rules same in $same_n of $loops loops; $failed of $(($# * 2)) arms failed"
[ $failed = 0 ]
