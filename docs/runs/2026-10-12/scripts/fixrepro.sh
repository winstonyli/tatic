# the rival-scoring fix (count-only) against HEAD's rows: full sweeps, salts 1-2
k=$(bash "$(dirname "$0")/kk.sh"); : > $k/fix_done.txt
run() { local salt=$1 out=$k/fix_$1 t0=$(date +%s); rm -rf $out; mkdir -p $out
  SWEEP_OUT=$out SALT=$salt SWEEP="mines own cold pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/bv_fix.exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "fix_$salt $(( $(date +%s) - t0 ))s" >> $k/fix_done.txt; }
run 1 & run 2 & wait
echo ALL >> $k/fix_done.txt
