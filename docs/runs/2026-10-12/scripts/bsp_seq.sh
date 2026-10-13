# usage: bsp_seq.sh: HEAD (a1ad219, bv_ha1ad.exe) against beta_spine reducing the spine's own head node plus args_id's
# stack buffer (bv_bsp.exe), one run at a time; order new, head on salt 1 and head, new on salt 2
k=$(cygpath -u "$TEMP")/kk; mkdir -p $k; rm -f $k/bss_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/bss_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/bss_done.txt; }
run bv_bsp.exe new 1; run bv_ha1ad.exe head 1; run bv_ha1ad.exe head 2; run bv_bsp.exe new 2
echo ALL >> $k/bss_done.txt
