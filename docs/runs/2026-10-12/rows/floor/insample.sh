#!/bin/sh
# $1 = loop dir (d_all_s<salt>/cold_<fam>_<p>_none); in-sample: mine on that loop's floor laws, then serve them again
cd "/c/Users/Winston Li/AppData/Local/Temp/oracle_probe"
src=$1; salt=$(echo $src | sed 's/d_all_s\([0-9]*\).*/\1/'); fam=$(echo $src | sed 's/.*cold_\([a-z0-9]*\)_.*/\1/'); p=$(echo $src | sed 's/.*_\([0-9]\)_none/\1/')
case $fam in cmp3d) st=15;; add3) st=7;; sbo3) st=11;; esac
w="floor/w_s${salt}_${fam}_$p"; mkdir -p $w
cat $src/serve_100.log $src/serve_200.log | grep -o "MACHINE [0-9]* .*" | cut -d' ' -f3- > $w/floor.txt
n=$(wc -l < $w/floor.txt); [ "$n" = 0 ] && { rm -r $w; exit 0; }
cp $src/rules.txt $w/rules.txt
export RULEMINER_FAMILY=$fam CHECK_FAMILY=$fam RULEMINER_DEEP3=1 RULEMINER_STRIDE=$st RULEMINER_PHASE=$p RULEMINER_SHAPE=2 MACHINE_BANNER=0 LEMMA_CACHE="$PWD/$w/lemmas.bin" RULEMINER_FAST=1 RULEMINER_SHUFFLE=$salt MIMALLOC_ALLOW_LARGE_OS_PAGES=0 CHECK_FAST=1
run() { cmd //c start "" //b //belownormal //affinity FFF //wait "$PWD/dose.exe" "$1" --exact --ignored --nocapture --test-threads 1 > "$2" 2>&1 < /dev/null; }
CHECK_RULES="$PWD/$w/rules.txt" CHECK_LAWFILE="$PWD/$w/floor.txt" run search::rule_set_kernel_check $w/before.log
RULEMINER_PERM=1 RULEMINER_THREADS=6 RULEMINER_ROUNDS=18446744073709551615 RULEMINER_BASE="$PWD/$w/rules.txt" RULEMINER_LAWFILE="$PWD/$w/floor.txt" run search::rule_miner $w/mine.log
grep -E "RULEMINER (chosen|prefer)" $w/mine.log | grep " -> " | sed 's/^.*): //' >> $w/rules.txt
CHECK_RULES="$PWD/$w/rules.txt" CHECK_LAWFILE="$PWD/$w/floor.txt" run search::rule_set_kernel_check $w/after.log
b=$(grep -c "MACHINE [0-9]" $w/before.log); a=$(grep -c "MACHINE [0-9]" $w/after.log)
echo "$salt $fam $p $n $b $a $(grep -c 'RULEMINER chosen' $w/mine.log)" >> floor/insample.tsv
rm -f $w/lemmas.bin
