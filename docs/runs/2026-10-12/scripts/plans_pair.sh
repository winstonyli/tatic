# usage: plans_pair.sh: plain decisions (bv_plain.exe, e49535f) and proof plans (bv_plans.exe) side by side, same load, salts 1 and 2
k=$(cygpath -u "$TEMP")/kk; rm -f $k/pp_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/pp_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/pp_done.txt; }
for salt in 1 2; do run bv_plans.exe plans $salt & run bv_plain.exe plain $salt & wait; done
echo ALL >> $k/pp_done.txt
