# usage: streq_pair.sh <salt>: HEAD (bv_it.exe, 22b9280) and structural equality (bv_streq.exe) side by side, same load
salt=$1
k=$(cygpath -u "$TEMP")/kk
run() { exe=$1; tag=$2; out=$k/sq_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/sq_done.txt; }
run bv_it.exe head & run bv_streq.exe streq & wait
