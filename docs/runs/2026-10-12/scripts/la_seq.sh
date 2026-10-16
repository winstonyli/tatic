# usage: la_seq.sh: as la_pair.sh (bv_base.exe 8f348b9 against bv_la.exe a045cfb), but one run at a time, so neither shares
# the 12 cores with the other; order la, head on salt 1 and head, la on salt 2
k=$(bash "$(dirname "$0")/kk.sh"); rm -f $k/las_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/las_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/las_done.txt; }
run bv_la.exe la 1; run bv_base.exe head 1; run bv_base.exe head 2; run bv_la.exe la 2
echo ALL >> $k/las_done.txt
