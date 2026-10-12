salt=$1; out="$TEMP/kk/du${TAG}_$salt"; rm -rf "$out"; mkdir -p "$out"
start=$(date +%s)
LIB=$TEMP/kk/sweep_f1_$salt SWEEP_OUT="$out" SALT=$salt SWEEP="pooled" cmd //c start "" //b //belownormal //wait "$TEMP/bv_du.exe" driver::sweep --exact --ignored --nocapture > "$out/log.txt" 2>&1
echo "du $salt $(( $(date +%s) - start ))s" >> "$TEMP/kk/du_done.txt"
