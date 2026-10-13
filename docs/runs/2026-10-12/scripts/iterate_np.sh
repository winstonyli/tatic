# iterated sweep from ABLATE=promoted: do the iterations recover the promoted rules' rows (own 74/102, pooled 58/99)?
# iteration 0 `mines own pooled`; iterations 1-3 `mines own pooled` seeded from the previous pooled libraries; salts 1-2 in parallel
k=$(cygpath -u "$TEMP")/kk; : > $k/np_it_done.txt
sweep() { local tag=$1 salt=$2; shift 2; local out=$k/$tag t0=$(date +%s); rm -rf $out; mkdir -p $out
  env "$@" ABLATE=promoted SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/bv_it.exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $(( $(date +%s) - t0 ))s" >> $k/np_it_done.txt; }
lane() { local s=$1; sweep npit0_$s $s X=1; for i in 1 2 3; do sweep npit${i}_$s $s MINES_WARM=$k/npit$((i-1))_$s; done; }
lane 1 & lane 2 & wait
echo ALL >> $k/np_it_done.txt
