# usage: sl_pair.sh: HEAD (bv_base.exe, ed00b7a) and one lemma file per sweep (bv_sl.exe) side by side, same load, salts 1 and 2
k=$(cygpath -u "$TEMP")/kk; rm -f $k/slp_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/slp_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/slp_done.txt; }
for salt in 1 2; do run bv_sl.exe sl $salt & run bv_base.exe head $salt & wait; done
echo ALL >> $k/slp_done.txt
