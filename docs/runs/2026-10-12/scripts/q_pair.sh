# usage: q_pair.sh: HEAD (bv_base.exe, 5c4618f) and one shared queue for the scoring workers within a chunk (bv_q.exe)
# side by side, same load, salts 1 and 2, no machine-state lines
k=$(cygpath -u "$TEMP")/kk; rm -f $k/qp_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/qp_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/qp_done.txt; }
for salt in 1 2; do run bv_q.exe q $salt & run bv_base.exe head $salt & wait; done
echo ALL >> $k/qp_done.txt
