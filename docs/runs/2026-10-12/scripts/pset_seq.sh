# usage: pset_seq.sh: HEAD (6cd8948, bv_head.exe) against the node table as a set of node pointers with their hashes
# (bv_pset.exe), one run at a time; order new, head on salt 1 and head, new on salt 2
k=$(cygpath -u "$TEMP")/kk; mkdir -p $k; rm -f $k/pss_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/pss_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/pss_done.txt; }
run bv_pset.exe new 1; run bv_head.exe head 1; run bv_head.exe head 2; run bv_pset.exe new 2
echo ALL >> $k/pss_done.txt
