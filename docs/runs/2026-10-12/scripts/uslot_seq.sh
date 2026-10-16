# usage: uslot_seq.sh: HEAD (7fe880f, bv_head.exe) against the last `uses` answer kept in the node header, with the
# per-scope `uses` table deleted (bv_uslot.exe), one run at a time; order new, head on salt 1 and head, new on salt 2
k=$(bash "$(dirname "$0")/kk.sh"); mkdir -p $k; rm -f $k/uss_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/uss_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/uss_done.txt; }
run bv_uslot.exe new 1; run bv_head.exe head 1; run bv_head.exe head 2; run bv_uslot.exe new 2
echo ALL >> $k/uss_done.txt
