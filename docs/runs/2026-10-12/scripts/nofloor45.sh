# drop-floor salts 4-5: pooled stage with the floor at 0 on the HEAD sweeps' libraries
k=$(bash "$(dirname "$0")/kk.sh"); rm -rf $k/s1791*_nofloor
for salt in 4 5; do out=$k/s${salt}_nofloor; rm -rf $out; mkdir -p $out; t0=$(date +%s)
  LIB=$k/s${salt}_head SWEEP_OUT=$out SALT=$salt SWEEP=pooled cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/bv_nofloor.exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "s${salt}_nofloor $(( $(date +%s) - t0 ))s" >> $k/order_done.txt; done
