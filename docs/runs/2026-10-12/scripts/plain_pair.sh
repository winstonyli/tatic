# usage: plain_pair.sh: HEAD (bv_head.exe, 2bf9c7a) and plain decisions (bv_plain.exe) side by side, same load, salts 1 and 2
k=$(cygpath -u "$TEMP")/kk; rm -f $k/pl_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/pl_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/pl_done.txt; }
for salt in 1 2; do run bv_head.exe head $salt & run bv_plain.exe plain $salt & wait; done
echo ALL >> $k/pl_done.txt
