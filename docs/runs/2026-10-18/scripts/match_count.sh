# match_count.sh <exe> <salt>: SWEEP=cold:cmp3d (extras on, 2 lanes) with patches/match_count.patch's counters; prints each
# mine's `RULEMINER probe` line and their sum (fields in the patch's header).
exe=$1; s=$2
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
t0=$(date +%s)
MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=$s SWEEP_OUT="$(cygpath -w "$d")" "$exe" driver::sweep --exact --ignored --nocapture > "$d/log.txt" 2>&1
echo "exit $? wall $(( $(date +%s) - t0 )) s"
grep -h "RULEMINER probe" "$d"/*/mine_*.log
grep -h "RULEMINER probe" "$d"/*/mine_*.log | tr -d '[],' | awk '{for (i = 3; i <= NF; i++) s[i] += $i} END {printf "sum"; for (i = 3; i <= NF; i++) printf " %d", s[i]; print ""}'
