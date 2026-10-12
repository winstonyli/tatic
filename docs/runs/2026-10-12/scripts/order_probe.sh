# operand-order probe (ORDER=rev|size, ABLATE=comm, default sanity) and drop-floor salts 4-5; three lanes, 12 cores total
k=$TEMP/kk; done_f=$k/order_done.txt; : > $done_f
run() { exe=$1; tag=$2; salt=$3; sweep=$4; shift 4; out=$k/$tag; rm -rf $out; mkdir -p $out; s=$(date +%s)
  env "$@" SWEEP_OUT=$out SALT=$salt SWEEP="$sweep" cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $(( $(date +%s) - s ))s" >> $done_f; }
all="mines own cold pooled"
laneA() { run bv_order.exe ord_rev_1 1 "$all" ORDER=rev; run bv_order.exe ord_rev_2 2 "$all" ORDER=rev; run bv_order.exe ord_size_1 1 "$all" ORDER=size; }
laneB() { run bv_order.exe ord_size_2 2 "$all" ORDER=size; run bv_order.exe ord_comm_1 1 "$all" ABLATE=comm; run bv_order.exe ord_comm_2 2 "$all" ABLATE=comm; }
laneC() { run bv_order.exe ord_def_1 1 "$all" X=1
  for s in 4 5; do run bv_head.exe s${s}_head $s "mines own pooled" X=1; run bv_nofloor.exe s${s}_nofloor $s pooled LIB=$k/s${s}_head; done; }
laneA & laneB & laneC & wait
echo ALL >> $done_f
