out=$TEMP/kk/s3_head; rm -rf $out; mkdir -p $out; s=$(date +%s)
SWEEP_OUT=$out SALT=3 SWEEP="mines own pooled" cmd //c start "" //b //belownormal //wait "$TEMP/bv_head.exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
echo "head $(( $(date +%s) - s ))s" >> $TEMP/kk/s3_done.txt
out2=$TEMP/kk/s3_nofloor; rm -rf $out2; mkdir -p $out2; s=$(date +%s)
LIB=$out SWEEP_OUT=$out2 SALT=3 SWEEP="pooled" cmd //c start "" //b //belownormal //wait "$TEMP/bv_nofloor.exe" driver::sweep --exact --ignored --nocapture > $out2/log.txt 2>&1
echo "nofloor $(( $(date +%s) - s ))s" >> $TEMP/kk/s3_done.txt
