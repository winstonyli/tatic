# usage: mot_seq.sh: HEAD (50ba04f; run as the prototype bv_mot.exe with OLDMOTIVE=1, HEAD's motives) against one shared
# motive per case tree (bv_new.exe), one run at a time; order new, head on salt 1 and head, new on salt 2; no machine-state lines
k=$(cygpath -u "$TEMP")/kk; mkdir -p $k; rm -f $k/mos_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/mos_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  if [ $tag = head ]; then export OLDMOTIVE=1; else unset OLDMOTIVE; fi
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/mos_done.txt; }
run bv_new.exe new 1; run bv_mot.exe head 1; run bv_mot.exe head 2; run bv_new.exe new 2
echo ALL >> $k/mos_done.txt
