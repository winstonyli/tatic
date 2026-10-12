salt=$1; out="$TEMP/kk/sweep_h_$salt"; rm -rf "$out"; mkdir -p "$out"
start=$(date +%s)
SWEEP_OUT="$out" SALT=$salt SWEEP="mines own cold pooled" cmd //c start "" //b //belownormal //wait "$TEMP/bv_sm2.exe" driver::sweep --exact --ignored --nocapture > "$out/log.txt" 2>&1
echo "h $salt $(( $(date +%s) - start ))s" >> "$TEMP/kk/sm_sweeps.txt"
