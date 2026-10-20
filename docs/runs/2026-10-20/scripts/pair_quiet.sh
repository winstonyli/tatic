# pair_quiet.sh <exe> <salt>: match_count.sh's run (SWEEP=cold:cmp3d, 2 lanes) once under `runs time`, so it starts
# only when other load is quiet; then each mine's `RULEMINER pair` line (join_order_pair.patch) and their sum.
exe=$1; s=$2
d=$(cygpath -w "$RUN_DIR")
"$(dirname "$0")/../../../../tools/runs/target/release/runs.exe" time "$d" --rounds 1 --max-hours 3 \
  -- pair MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=$s "SWEEP_OUT=$d\{arm}_{r}" "$exe" driver::sweep --exact --ignored --nocapture < /dev/null
cat "$RUN_DIR"/pair_*/*/mine_*.log | grep "RULEMINER pair"
cat "$RUN_DIR"/pair_*/*/mine_*.log | grep "RULEMINER pair" | tr -d '[],' | awk '{for (i = 3; i <= NF; i++) s[i] += $i} END {printf "sum"; for (i = 3; i <= NF; i++) printf " %d", s[i]; print ""}'
