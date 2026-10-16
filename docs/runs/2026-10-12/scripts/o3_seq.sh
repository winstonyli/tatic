# usage: o3_seq.sh: HEAD (bv_base.exe, e9a8be1) against three rounds kept open while their winners are proved (bv_o3.exe),
# one run at a time; order o3, head on salt 1 and head, o3 on salt 2; no machine-state lines
k=$(bash "$(dirname "$0")/kk.sh"); rm -f $k/o3s_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/o3s_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/o3s_done.txt; }
run bv_o3.exe o3 1; run bv_base.exe head 1; run bv_base.exe head 2; run bv_o3.exe o3 2
echo ALL >> $k/o3s_done.txt
