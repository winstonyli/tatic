# usage: aid_seq.sh: HEAD (01018d6, bv_h1018.exe) against args_id taking canonical arguments' own addresses (bv_aid.exe),
# one run at a time; order new, head on salt 1 and head, new on salt 2
k=$(cygpath -u "$TEMP")/kk; mkdir -p $k; rm -f $k/ais_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/ais_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/ais_done.txt; }
run bv_aid.exe new 1; run bv_h1018.exe head 1; run bv_h1018.exe head 2; run bv_aid.exe new 2
echo ALL >> $k/ais_done.txt
