# sweeps with each re-promoted set in place of PROMOTED, under its own operand order; salts 1-2, two at a time
k=$(bash "$(dirname "$0")/kk.sh"); : > $k/ps_done.txt
run() { local order=$1 salt=$2 out=$k/ps_${1}_$2 t0=$(date +%s); rm -rf $out; mkdir -p $out
  PROMOTED_FILE=$k/promo/$order.rules ORDER=$order SWEEP_OUT=$out SALT=$salt SWEEP="mines own cold pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/bv_promo.exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "ps_${order}_$salt $(( $(date +%s) - t0 ))s" >> $k/ps_done.txt; }
run show 1 & run show 2 & wait
run size 1 & run size 2 & wait
echo ALL >> $k/ps_done.txt
