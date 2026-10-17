#!/bin/sh
# $1 = bucket (past|future|novel|unseen|random), $2 = salt; twin-free, add3 60 / sbo3 180 / cmp3d 350 extras
cd "/c/Users/Winston Li/AppData/Local/Temp/oracle_probe"
[ "$1" = random ] || export MINE_BUCKET=$1
export MINE_TWINFREE=1 MINE_EXTRA=add3:60,sbo3:180,cmp3d:350 SWEEP_OUT="$PWD/b_$1_s$2" SWEEP="cold" SALT=$2
s=$(date +%s)
cmd //c start "" //b //belownormal //affinity FFF //wait "$PWD/bucket.exe" driver::sweep --ignored --nocapture --test-threads 1 > "b_$1_s$2.log" 2>&1
echo "$1 s$2 exit $? $(( $(date +%s) - s ))s" >> bucket.done
