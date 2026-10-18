# join_check.sh <exe> <salt>: SWEEP=cold:cmp3d (extras on, 2 lanes) with JOIN_CHECK=1 (patches/join_check2.patch): on every
# join memo hit the search is rerun under the rules in force, counting flips (met against failed) and hits whose fresh
# trace differs from the kept one. Prints the last JOIN_CHECK line per mine log and the totals of the last lines.
exe=$1; s=$2
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
t0=$(date +%s)
JOIN_CHECK=1 MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=$s SWEEP_OUT="$(cygpath -w "$d")" "$exe" driver::sweep --exact --ignored --nocapture > "$d/log.txt" 2>&1
echo "exit $? wall $(( $(date +%s) - t0 )) s"
grep -rl "JOIN_CHECK hits" "$d" --include=*.log | while read -r f; do echo "${f#"$d"/}: $(grep "JOIN_CHECK hits" "$f" | tail -1)"; done
grep -rh "JOIN_CHECK hits.*: " "$d" | head -20
