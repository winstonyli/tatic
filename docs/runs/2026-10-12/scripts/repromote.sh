# re-promotion under each operand order (ORDER=show|size), no promoted rules in force while mining; section-60 procedure:
# round 1 mines mul/shl/lt, round 2 mines mul/shl/lt/shr with round 1's rules in force; every chosen rule is promoted
k=$(cygpath -u "$TEMP")/kk/promo; rm -rf $k; mkdir -p $k; : > $k/empty.txt   # a Unix path: globs do not expand under $TEMP's backslashes
mine() { local order=$1 fam=$2 round=$3 base=$4; shift 4; local log=$k/${order}_r${round}_$fam.log t0=$(date +%s)
  env "$@" RULEMINER_FAMILY=$fam RULEMINER_BASE=$base PROMOTED_FILE=$k/empty.txt ORDER=$order RULEMINER_THREADS=2 cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/bv_promo.exe" search::rule_miner --exact --ignored --nocapture > $log 2>&1
  echo "$order r$round $fam $(( $(date +%s) - t0 ))s" >> $k/done.txt; }
chosen() { grep -h "RULEMINER chosen" "$@" | grep -- " -> " | sed 's/^.*): //'; }
lane() { local o=$1
  mine $o mul 1 $k/empty.txt MULMINER_MAX=5 & mine $o shl 1 $k/empty.txt RULEMINER_LAWS=300 & mine $o lt 1 $k/empty.txt RULEMINER_LAWS=150 & wait
  chosen $k/${o}_r1_*.log > $k/${o}_r1.rules
  mine $o mul 2 $k/${o}_r1.rules MULMINER_MAX=5 & mine $o shl 2 $k/${o}_r1.rules RULEMINER_LAWS=300 & mine $o lt 2 $k/${o}_r1.rules RULEMINER_LAWS=150 &
  mine $o shr 2 $k/${o}_r1.rules RULEMINER_DEEP=1 MINER_SUB=1 RULEMINER_STRIDE=3 RULEMINER_LAWS=900 & wait
  { cat $k/${o}_r1.rules; chosen $k/${o}_r2_*.log; } > $k/${o}.rules
  echo "$o promoted $(wc -l < $k/${o}.rules)" >> $k/done.txt; }
: > $k/done.txt
lane show & lane size & wait
echo ALL >> $k/done.txt
