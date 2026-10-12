# usage: pair_sweep.sh <salt>: HEAD and the 6ca89b3 baseline side by side, same load
salt=$1
run() { exe=$1; tag=$2; out="$TEMP/kk/pair_${tag}_$salt"; rm -rf "$out"; mkdir -p "$out"; s=$(date +%s)
  SWEEP_OUT="$out" SALT=$salt SWEEP="mines own cold pooled" cmd //c start "" //b //belownormal //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > "$out/log.txt" 2>&1
  echo "$tag $salt $(( $(date +%s) - s ))s" >> "$TEMP/kk/pair_done.txt"; }
run bv_head.exe head & run bv_kf.exe base & wait
