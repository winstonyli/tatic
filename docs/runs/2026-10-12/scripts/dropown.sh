# candidate 2 probe: preferences in every mine (control) vs plus drops of the mine's own rules, salts 1-2, two lanes
k=$TEMP/kk; done_f=$k/dropown_done.txt; : > $done_f
run() { local tag=$1 salt=$2 own=$3 out=$k/do_$1 t0=$(date +%s); rm -rf $out; mkdir -p $out
  RULEMINER_PREFS=1 RULEMINER_DROP_OWN=$own SWEEP_OUT=$out SALT=$salt SWEEP="mines own cold pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/bv_dropown.exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "do_$tag $(( $(date +%s) - t0 ))s" >> $done_f; }
{ run prefs_1 1 0; run prefs_2 2 0; } & { run own_1 1 1; run own_2 2 1; } & wait
echo ALL >> $done_f
