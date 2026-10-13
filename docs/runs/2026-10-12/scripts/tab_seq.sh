# usage: tab_seq.sh: HEAD (51cd960; run as the prototype bv_tab.exe with NOTABMEMO=1, HEAD's table_app) against truth
# tables built once per generation (bv_tabn.exe), one run at a time; order new, head on salt 1 and head, new on salt 2
k=$(cygpath -u "$TEMP")/kk; mkdir -p $k; rm -f $k/tbs_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/tbs_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  if [ $tag = head ]; then export NOTABMEMO=1; else unset NOTABMEMO; fi
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/tbs_done.txt; }
run bv_tabn.exe new 1; run bv_tab.exe head 1; run bv_tab.exe head 2; run bv_tabn.exe new 2
echo ALL >> $k/tbs_done.txt
