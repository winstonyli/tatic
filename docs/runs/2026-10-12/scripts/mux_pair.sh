# usage: mux_pair.sh: HEAD (bv_head.exe, 9f1d23e) and the one-gate mux and not (bv_mux.exe) side by side, same load, salts 1 and 2
k=$(cygpath -u "$TEMP")/kk; rm -f $k/mx_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/mx_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/mx_done.txt; }
for salt in 1 2; do run bv_mux.exe mux $salt & run bv_head.exe head $salt & wait; done
echo ALL >> $k/mx_done.txt
