# sm_sweep.sh <salt>: the sweep (stages mines own cold pooled) of bv_sm2.exe for one salt; seconds appended to sm_sweeps.txt.
salt=$1; out="$(bash "$(dirname "$0")/kk.sh")/sweep_h_$salt"; rm -rf "$out"; mkdir -p "$out"
start=$(date +%s)
SWEEP_OUT="$out" SALT=$salt SWEEP="mines own cold pooled" cmd //c start "" //b //belownormal //wait "$TEMP/bv_sm2.exe" driver::sweep --exact --ignored --nocapture > "$out/log.txt" 2>&1
echo "h $salt $(( $(date +%s) - start ))s" >> "$(bash "$(dirname "$0")/kk.sh")/sm_sweeps.txt"
