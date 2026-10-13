# usage: dd_seq.sh: HEAD (bv_base.exe, 84242e0) against case trees up to nv = 9 (DDMIN default 10, bv_dd.exe), one run at a
# time; order dd, head on salt 1 and head, dd on salt 2; no machine-state lines
k=$(cygpath -u "$TEMP")/kk; rm -f $k/dds_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/dds_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/dds_done.txt; }
run bv_dd.exe dd 1; run bv_base.exe head 1; run bv_base.exe head 2; run bv_dd.exe dd 2
echo ALL >> $k/dds_done.txt
