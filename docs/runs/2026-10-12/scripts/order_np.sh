# operand-order probe without the promoted rules (ABLATE=promoted), three orders x salts 1-2, three lanes, 12 cores total
k=$TEMP/kk; done_f=$k/order_np_done.txt; : > $done_f
run() { local tag=$1 salt=$2 order=$3 out=$k/np_$1 t0=$(date +%s); rm -rf $out; mkdir -p $out
  ABLATE=promoted ORDER=$order SWEEP_OUT=$out SALT=$salt SWEEP="mines own cold pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/bv_order.exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "np_$tag $(( $(date +%s) - t0 ))s" >> $done_f; }
{ run show_1 1 show; run show_2 2 show; } & { run rev_1 1 rev; run rev_2 2 rev; } & { run size_1 1 size; run size_2 2 size; } & wait
echo ALL >> $done_f
