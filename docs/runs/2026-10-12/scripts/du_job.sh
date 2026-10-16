salt=$1; out="$(bash "$(dirname "$0")/kk.sh")/du${TAG}_$salt"; rm -rf "$out"; mkdir -p "$out"
start=$(date +%s)
LIB=$(bash "$(dirname "$0")/kk.sh")/sweep_f1_$salt SWEEP_OUT="$out" SALT=$salt SWEEP="pooled" cmd //c start "" //b //belownormal //wait "$TEMP/bv_du.exe" driver::sweep --exact --ignored --nocapture > "$out/log.txt" 2>&1
echo "du $salt $(( $(date +%s) - start ))s" >> "$(bash "$(dirname "$0")/kk.sh")/du_done.txt"
