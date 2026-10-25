#!/bin/bash
# probe.sh: throwaway frontier probe (2026-10-24). Per growth count in $LEVELS: the HELD_SALT sequence and its bands
# (P.exe classes::probe_frontier, stopped past 8 GB private commit), then each band's held-out M under salt 6's three
# loop rules (run cache-check-1) and under no rules. Output under $RUN_DIR.
src=$(dirname "$(readlink -f "$0")"); out=$(cygpath -u "$RUN_DIR"); root="/c/Users/Winston Li/Documents/GitHub/tatic"
mem() { powershell -NoProfile -File "$(cygpath -w "$root/scripts/tree_mem.ps1")" -Match "$1" "${@:2}" < /dev/null | tr -d '\r'; }
for lv in ${LEVELS:-3 4}; do
  d="$out/levels_$lv"; mkdir -p "$d"; peak=0; t0=$(date +%s)
  ( MACHINE_STATE=0 PROBE_LEVELS=$lv PROBE_OUT="$(cygpath -w "$d")" "$src/P.exe" classes::probe_frontier --exact --ignored --nocapture < /dev/null > "$d/gen.txt" 2>&1; echo $? > "$d/exit" ) &
  while [ ! -f "$d/exit" ]; do
    mb=$(mem "$(cygpath -w "$d")"); [ "${mb:-0}" -gt "$peak" ] && peak=$mb
    [ "${mb:-0}" -gt 8192 ] && { echo "levels $lv: over 8 GB ($mb MB), stopped"; mem "$(cygpath -w "$d")" -Kill > /dev/null; }
    ping -n 3 127.0.0.1 > /dev/null
  done
  echo "levels $lv: exit $(cat "$d/exit") in $(( $(date +%s) - t0 )) s, peak commit ~${peak} MB (2 s samples)"; grep '^PROBE' "$d/gen.txt"
  [ "$(cat "$d/exit")" = 0 ] || continue
  for f in "$d"/held_*.txt; do
    b=$(basename "$f" .txt); b=${b#held_}; [ "$(grep -c ' = ' "$f")" -gt 0 ] || continue
    for r in 1 2 3 none; do
      line=$(MACHINE_STATE=0 CHECK_FAST=1 CHECK_FAMILY=streams CHECK_RULES="$(cygpath -w "$src/rules_$r.txt")" CHECK_LAWFILE="$(cygpath -w "$f")" \
        "$src/P.exe" search::rule_set_kernel_check --exact --ignored --nocapture < /dev/null 2>&1 | grep '^CHECKED ')
      p=$(echo "$line" | sed -E 's/^CHECKED ([0-9]+) .*/\1/'); fr=$(echo "$line" | sed -E 's/.*\(([0-9]+) with.*/\1/'); n=$(echo "$line" | sed -E 's/.*\), ([0-9]+) not proved.*/\1/')
      echo "levels $lv band $b rules $r: laws $(grep -c ' = ' "$f") M $((p - fr + n)) | $line"
    done
  done
done
