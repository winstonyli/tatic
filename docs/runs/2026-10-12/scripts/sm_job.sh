for m in 0 1 0 1; do
  i=$((i+1)); d=$(bash "$(dirname "$0")/kk.sh")/sm${m}_$i; rm -rf $d; mkdir -p $d
  s=$(date +%s)
  RULEMINER_STATE_MEMO=$m LOOP_MODE=loop LOOP_OUT=$d FAMILY=cmp3d STRIDE=15 SPHASE=3 B=100 K=3 OFFSET=0 THREADS=6 CHECK_FAST=1 MACHINE_STATE=0 RULEMINER_FAST=1 RULEMINER_SHUFFLE=1 cmd //c start "" //b //belownormal //wait $TEMP/bv_sm.exe driver::loop_stream --exact --ignored --nocapture > $d/out.log 2>&1
  echo "memo=$m run $i wall $(( $(date +%s) - s ))s" >> $(bash "$(dirname "$0")/kk.sh")/sm_times.txt
done
