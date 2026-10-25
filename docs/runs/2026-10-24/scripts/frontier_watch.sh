#!/bin/bash
# watch.sh <run dir>: until the run's levels_4/exit exists (deadline 30 min), sample probe_frontier's tree commit every 2 s, stop it past 8 GB; prints the peak
root="/c/Users/Winston Li/Documents/GitHub/tatic"; d=$1; peak=0; end=$(( $(date +%s) + 1800 ))
while [ ! -f "$d/levels_4/exit" ] && [ $(date +%s) -lt $end ]; do
  mb=$(powershell -NoProfile -File "$(cygpath -w "$root/scripts/tree_mem.ps1")" -Match "classes::probe_frontier" < /dev/null | tr -d '\r')
  [ "${mb:-0}" -gt "$peak" ] && peak=$mb
  [ "${mb:-0}" -gt 8192 ] && { echo "over 8 GB ($mb MB), stopping"; powershell -NoProfile -File "$(cygpath -w "$root/scripts/tree_mem.ps1")" -Match "classes::probe_frontier" -Kill < /dev/null > /dev/null; }
  ping -n 3 127.0.0.1 > /dev/null
done
echo "levels 4 peak commit ~$peak MB"
