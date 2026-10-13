# usage: ctab_seq.sh: HEAD (8334948, bv_whnf.exe) against a const-initialized thread-local table and interning
# without moving the node through the table's closure (bv_ctab.exe), one run at a time; order new, head on salt 1 and head, new on salt 2
k=$(cygpath -u "$TEMP")/kk; mkdir -p $k; rm -f $k/cts_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/cts_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/cts_done.txt; }
run bv_ctab.exe new 1; run bv_whnf.exe head 1; run bv_whnf.exe head 2; run bv_ctab.exe new 2
echo ALL >> $k/cts_done.txt
