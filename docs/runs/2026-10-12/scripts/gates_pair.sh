# usage: gates_pair.sh: HEAD (bv_head.exe, e1d28d9) and the gate-constant cache (bv_gates.exe) side by side, same load, salts 1 and 2
k=$(bash "$(dirname "$0")/kk.sh"); rm -f $k/gc_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/gc_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/gc_done.txt; }
for salt in 1 2; do run bv_gates.exe gates $salt & run bv_head.exe head $salt & wait; done
echo ALL >> $k/gc_done.txt
