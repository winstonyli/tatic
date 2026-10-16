# usage: sp_pair.sh: HEAD (bv_base.exe, 99475ac) and the two-variable candidate index plus the sequence kept per salt (bv_sp.exe)
# side by side, same load, salts 1 and 2, no machine-state lines
k=$(bash "$(dirname "$0")/kk.sh"); rm -f $k/spp_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/spp_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/spp_done.txt; }
for salt in 1 2; do run bv_sp.exe sp $salt & run bv_base.exe head $salt & wait; done
echo ALL >> $k/spp_done.txt
