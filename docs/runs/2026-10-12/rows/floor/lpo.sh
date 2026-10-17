#!/bin/sh
# $1 = mode (none|tied|all); M on the floor laws (in-sample libraries) and on the served batches 1-2 (loop libraries), dose all
cd "/c/Users/Winston Li/AppData/Local/Temp/oracle_probe"
m() { FLOOR_LPO=$1 CHECK_FAMILY=$2 RULEMINER_FAMILY=$2 CHECK_FAST=1 RULEMINER_FAST=1 CHECK_RULES="$PWD/$3" CHECK_LAWFILE="$PWD/$4" ./lpo.exe search::rule_set_kernel_check --exact --ignored --nocapture --test-threads 1 < /dev/null 2>&1 | grep -o "CHECKED.*" | tr -c '0-9
' ' ' | awk '{print $1 - $2 + $3, $4}'; }
for w in floor/w_*; do fam=$(echo $w | sed 's/.*w_s[0-9]*_\([a-z0-9]*\)_.*/\1/'); echo "floor $fam $(m $1 $fam $w/rules.txt $w/floor.txt)"; done
for L in d_all_s*/cold_*; do fam=$(echo $L | sed 's/.*cold_\([a-z0-9]*\)_.*/\1/'); cat $L/laws_serve_100.txt $L/laws_serve_200.txt > $L/laws_served12.txt; echo "served $fam $(m $1 $fam $L/rules.txt $L/laws_served12.txt)"; done
