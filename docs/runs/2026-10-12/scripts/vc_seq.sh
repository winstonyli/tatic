# usage: vc_seq.sh: HEAD (bv_base.exe, 84242e0) against winner verdicts kept in the sweep's lemma file (bv_vc.exe), one run
# at a time; order vc, head on salt 1 and head, vc on salt 2; no machine-state lines
k=$(bash "$(dirname "$0")/kk.sh"); rm -f $k/vcs_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/vcs_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/vcs_done.txt; }
run bv_vc.exe vc 1; run bv_base.exe head 1; run bv_base.exe head 2; run bv_vc.exe vc 2
echo ALL >> $k/vcs_done.txt
