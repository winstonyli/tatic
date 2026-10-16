# usage: cap_ab.sh: mul_conjecture_miner (MULMINER_MAX=7, all 91 mul laws, CARRY_CAP 10) on 5f65267 (bv_old.exe, diagram
# lemmas at nv >= 10) against 0cb4e6c (bv_head.exe, case trees only), one run at a time, order old head head old
k=$(bash "$(dirname "$0")/kk.sh"); mkdir -p $k; rm -f $k/cap_done.txt
run() { exe=$1; tag=$2; i=$3; out=$k/cap_${tag}_$i.txt; s=$(date +%s)
  MULMINER_MAX=7 cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" machine::mul_conjecture_miner --exact --ignored --nocapture > $out 2>&1
  echo "$tag $i $(( $(date +%s) - s ))s $(grep 'MULMINER [0-9]* laws' $out)" >> $k/cap_done.txt; }
run bv_old.exe old 1; run bv_head.exe head 1; run bv_head.exe head 2; run bv_old.exe old 2
echo ALL >> $k/cap_done.txt
