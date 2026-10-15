# usage: hc_seq.sh <tag> <old exe> <new exe>: Term hash-consing, one sweep at a time (SWEEP="mines own cold pooled"), order new,
# old on salt 1 and old, new on salt 2, into $TEMP/kk/<tag>_{old,new}_{1,2}; "<tag> ALL" in $TEMP/kk/hc_done.txt at the end.
tag=$1; old=$2; new=$3
k=$(cygpath -u "$TEMP")/kk; mkdir -p $k; touch $k/hc_done.txt; sed -i "/^$tag /d" $k/hc_done.txt
run() { exe=$1; arm=$2; salt=$3; out=$k/${tag}_${arm}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own cold pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $arm $salt $(( $(date +%s) - s ))s" >> $k/hc_done.txt; }
run "$new" new 1; run "$old" old 1; run "$old" old 2; run "$new" new 2
echo "$tag ALL" >> $k/hc_done.txt
