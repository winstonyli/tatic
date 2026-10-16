# usage: stage2_seq.sh: id arena Stage 2. 4769775 (bv_s2_old.exe) against the branch id-arena-stage2 (bv_s2_new.exe:
# PExpr, persist, scoped and Escape on today's nodes), one run at a time; order new, old on salt 1 and old, new on
# salt 2. Then one salt-1 run of the branch built with --features copy-volume (bv_s2_cv.exe), whose children print
# COPYVOL lines.
k=$(bash "$(dirname "$0")/kk.sh"); mkdir -p $k; rm -f $k/s2_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/s2_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/s2_done.txt; }
run bv_s2_new.exe new 1; run bv_s2_old.exe old 1; run bv_s2_old.exe old 2; run bv_s2_new.exe new 2
run bv_s2_cv.exe cv 1
echo ALL >> $k/s2_done.txt
