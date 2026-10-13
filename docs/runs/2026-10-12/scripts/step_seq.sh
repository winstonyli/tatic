# usage: step_seq.sh: HEAD (4da7e02, bv_h7e02.exe) against the generation-memo helper plus the step memo (bv_sm.exe), one run
# at a time; order new, head on salt 1 and head, new on salt 2
k=$(cygpath -u "$TEMP")/kk; mkdir -p $k; rm -f $k/sts_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/sts_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/sts_done.txt; }
run bv_sm.exe new 1; run bv_h7e02.exe head 1; run bv_h7e02.exe head 2; run bv_sm.exe new 2
echo ALL >> $k/sts_done.txt
