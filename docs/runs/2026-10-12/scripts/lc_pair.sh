# usage: lc_pair.sh: HEAD (bv_head.exe, 639cdcd) and the trusted lemma cache (bv_lc.exe) side by side, same load, salts 1 and 2
k=$(bash "$(dirname "$0")/kk.sh"); rm -f $k/lcp_done.txt
run() { exe=$1; tag=$2; salt=$3; out=$k/lcp_${tag}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> $k/lcp_done.txt; }
for salt in 1 2; do run bv_lc.exe cache $salt & run bv_head.exe head $salt & wait; done
echo ALL >> $k/lcp_done.txt
