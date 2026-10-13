# usage: nodd_seq.sh: HEAD (5f65267; run as bv_wide.exe, HEAD plus an appended ignored nv = 11 probe test) against the
# decision-diagram path deleted (bv_nodd.exe), one run at a time; order new, head on salt 1 and head, new on salt 2
k=$(cygpath -u "$TEMP")/kk; mkdir -p $k; rm -f $k/nds_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/nds_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/nds_done.txt; }
run bv_nodd.exe new 1; run bv_wide.exe head 1; run bv_wide.exe head 2; run bv_nodd.exe new 2
echo ALL >> $k/nds_done.txt
