# join_cap.sh <exe> <salt>...: full sweeps (mines own cold pooled) of one build at join visit caps JOIN_VISIT = 5000, 1000, 300
# and with the join off (ABLATE=join), two sweeps side by side (each loop runs 6 threads), into kk.sh's directory ($RUN_DIR
# under run.ps1): <arm>_<salt>/ holds the sweep's stage files (mines.tsv: column 3 is M; the loop stages': column 4), its log,
# and its exit code and wall seconds.
exe=$1; shift
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
one() { # <arm> <salt> <VAR=val>
  o="$d/$1_$2"; mkdir -p "$o"; t0=$(date +%s)
  env "$3" MACHINE_STATE=0 SALT=$2 SWEEP="mines own cold pooled" SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1
  echo "$? $(( $(date +%s) - t0 ))" > "$o/exit_secs"
}
for s in "$@"; do
  one v5000 $s JOIN_VISIT=5000 & one off $s ABLATE=join & wait
  one v1000 $s JOIN_VISIT=1000 & one v300 $s JOIN_VISIT=300 & wait
  for arm in off v300 v1000 v5000; do
    o="$d/${arm}_$s"; m=""
    for t in mines own cold pooled; do
      c=4; [ $t = mines ] && c=3
      m="$m $t $(awk -F'\t' -v c=$c '{m+=$c} END {print m+0}' "$o/$t.tsv")"
    done
    echo "salt $s $arm: M$m, exit+secs $(cat "$o/exit_secs")"
  done
done
