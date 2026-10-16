# iterated sweep, continued: the existing pooled stage on iteration k's libraries, then iteration k+1 (`mines own`) seeded from it
k=$(bash "$(dirname "$0")/kk.sh"); : > $k/it2_done.txt
pooled() { local dir=$1 salt=$2 t0=$(date +%s)
  SWEEP_OUT=$dir SALT=$salt SWEEP=pooled cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/bv_it.exe" driver::sweep --exact --ignored --nocapture > $dir/log_pooled.txt 2>&1
  echo "$(basename $dir) pooled $(( $(date +%s) - t0 ))s" >> $k/it2_done.txt; }
iter() { local tag=$1 salt=$2 from=$3 out=$k/$1 t0=$(date +%s); rm -rf $out; mkdir -p $out
  MINES_WARM=$from SWEEP_OUT=$out SALT=$salt SWEEP="mines own" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/bv_it.exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $(( $(date +%s) - t0 ))s" >> $k/it2_done.txt; }
lane() { local s=$1; pooled $k/it1_$s $s; iter it2_$s $s $k/it1_$s; pooled $k/it2_$s $s; }
lane 1 & lane 2 & wait
echo ALL >> $k/it2_done.txt
