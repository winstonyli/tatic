# lookahead over the winner's rival, the winner and the runner-up, chosen by held-out finished value (2 folds); salts 1-2
k=$(bash "$(dirname "$0")/kk.sh"); : > $k/ho_done.txt
run() { local salt=$1 out=$k/ho_$1 t0=$(date +%s); rm -rf $out; mkdir -p $out
  SWEEP_OUT=$out SALT=$salt SWEEP="mines own cold pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/bv_ho.exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "ho_$salt $(( $(date +%s) - t0 ))s" >> $k/ho_done.txt; }
run 1 & run 2 & wait
echo ALL >> $k/ho_done.txt
