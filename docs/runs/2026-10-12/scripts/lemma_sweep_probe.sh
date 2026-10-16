# usage: lemma_sweep_probe.sh: 84072cd + a temporary LEMMA_SWEEP switch (one lemma file for the whole sweep; reverted) as
# bv_probe.exe, with (A) and without (B) the switch, side by side on the same salt-1 libraries (lib_* copied into both dirs)
k=$(bash "$(dirname "$0")/kk.sh"); rm -f $k/lsp_done.txt
run() { tag=$1; out=$k/lsp_$tag; s=$(date +%s)
  SWEEP_OUT=$out SALT=1 SWEEP="own pooled" $2 cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/bv_probe.exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $(( $(date +%s) - s ))s" >> $k/lsp_done.txt; }
run A "env LEMMA_SWEEP=$(cygpath -w $k/lsp_A/lemmas.bin)" & run B "env" & wait
echo ALL >> $k/lsp_done.txt
