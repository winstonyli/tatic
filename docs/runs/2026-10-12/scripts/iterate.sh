# promotion as an iterated sweep, falsifier: iteration 0 = HEAD `mines pooled`; iteration 1 = `mines own` with each ref mine
# seeded from iteration 0's pooled library for its family (MINES_WARM); salts 1-2 in parallel
k=$(cygpath -u "$TEMP")/kk; mkdir -p $k; : > $k/it_done.txt
sweep() { local tag=$1 salt=$2 stages=$3; shift 3; local out=$k/$tag t0=$(date +%s); rm -rf $out; mkdir -p $out
  env "$@" SWEEP_OUT=$out SALT=$salt SWEEP="$stages" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/bv_it.exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $(( $(date +%s) - t0 ))s" >> $k/it_done.txt; }
lane() { local s=$1; sweep it0_$s $s "mines pooled" X=1; sweep it1_$s $s "mines own" MINES_WARM=$k/it0_$s; }
lane 1 & lane 2 & wait
echo ALL >> $k/it_done.txt
