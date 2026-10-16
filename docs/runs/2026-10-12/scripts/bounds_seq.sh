# usage: bounds_seq.sh: 981540b (bv_bnd_old.exe) against 1bb3a5c, `uses` with the slot in front of per-scope (node, d)
# bounds (bv_bnd_new.exe), one run at a time; order new, old on salt 1 and old, new on salt 2
k=$(bash "$(dirname "$0")/kk.sh"); mkdir -p $k; rm -f $k/bnd_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/bnd_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/bnd_done.txt; }
run bv_bnd_new.exe new 1; run bv_bnd_old.exe old 1; run bv_bnd_old.exe old 2; run bv_bnd_new.exe new 2
echo ALL >> $k/bnd_done.txt
