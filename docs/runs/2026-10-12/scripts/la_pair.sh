# usage: la_pair.sh: HEAD (bv_base.exe, 8f348b9) and the ref mines on 6 scoring threads plus lookahead's winners proved in
# the background (bv_la.exe) side by side, same load, salts 1 and 2, no machine-state lines
k=$(bash "$(dirname "$0")/kk.sh"); rm -f $k/lap_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/lap_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/lap_done.txt; }
for salt in 1 2; do run bv_la.exe la $salt & run bv_base.exe head $salt & wait; done
echo ALL >> $k/lap_done.txt
