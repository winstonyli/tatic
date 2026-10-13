# usage: slim_seq.sh: HEAD (9fab09a, bv_head.exe) against the memos storing only their results, with non-canonical
# sources kept alive in one list (bv_slim.exe), one run at a time; order new, head on salt 1 and head, new on salt 2
k=$(cygpath -u "$TEMP")/kk; mkdir -p $k; rm -f $k/sls_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/sls_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/sls_done.txt; }
run bv_slim.exe new 1; run bv_head.exe head 1; run bv_head.exe head 2; run bv_slim.exe new 2
echo ALL >> $k/sls_done.txt
