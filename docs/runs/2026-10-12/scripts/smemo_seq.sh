# usage: smemo_seq.sh: HEAD (ff3eb86, as bv_uslot.exe) against one shift memo: cong1, trans_proof and cong_n shift
# through the interning table in a scope of their own, ShiftMemo deleted (bv_smemo.exe); new, head on salt 1, head, new on salt 2
k=$(bash "$(dirname "$0")/kk.sh"); mkdir -p $k; rm -f $k/sms_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/sms_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/sms_done.txt; }
run bv_smemo.exe new 1; run bv_uslot.exe head 1; run bv_uslot.exe head 2; run bv_smemo.exe new 2
echo ALL >> $k/sms_done.txt
