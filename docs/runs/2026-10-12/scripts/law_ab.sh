# law_ab.sh <old exe> <new exe> <pairs> <n>...: rule 33's law check time (church_bv `rewrite::law_time`), old and new
# alternating (old first on odd pairs), each run pinned to 12 cores at BelowNormal; LAW_REPS (default 5) reps per run.
# Appends "<tag> LAWT ..." lines to $TEMP/kk/law_ab.txt, then "ALL". Id arena Stage 3 (plan 2026-10-14-id-arena-stage3).
old=$1; new=$2; pairs=$3; shift 3
k=$(cygpath -u "$TEMP")/kk; mkdir -p $k; out=$k/law_ab.txt; : > $out
run() { LAW_N=$2 LAW_REPS=${LAW_REPS:-5} cmd //c start "" //b //belownormal //affinity FFF //wait "$1" rewrite::law_time --exact --ignored --nocapture > $k/law_run.txt 2>&1
  grep '^LAWT' $k/law_run.txt | sed "s/^/$3 /" >> $out; }
for n in "$@"; do for i in $(seq 1 $pairs); do
  if [ $((i % 2)) = 1 ]; then run "$old" $n old; run "$new" $n new; else run "$new" $n new; run "$old" $n old; fi
done; done
echo ALL >> $out
