#!/bin/sh
# $1 = orientation (fwd|back|down); per in-sample floor dir: add each remaining law's normal-form pair as a rule, then M on
# the floor laws and on the loop's mined batches (served12) with the library before and after
cd "/c/Users/Winston Li/AppData/Local/Temp/oracle_probe"
m() { CHECK_FAMILY=$1 RULEMINER_FAMILY=$1 CHECK_FAST=1 RULEMINER_FAST=1 CHECK_RULES="$PWD/$2" CHECK_LAWFILE="$PWD/$3" ./dose.exe search::rule_set_kernel_check --exact --ignored --nocapture --test-threads 1 < /dev/null 2>&1 | grep -o "CHECKED.*" | tr -c '0-9\n' ' ' | awk '{print $1 - $2 + $3}'; }
for w in $(cut -f2 floor/diag.tsv | sort -u); do
  fam=$(echo $w | sed 's/.*w_s[0-9]*_\([a-z0-9]*\)_.*/\1/'); src=$(echo $w | sed 's/floor\/w_s\([0-9]*\)_\([a-z0-9]*\)_\([0-9]\)/d_all_s\1\/cold_\2_\3_none/')
  cp $w/rules.txt $w/rules_c.txt
  awk -F'\t' -v w=$w -v o=$1 '$2==w { a=$8; b=$9; if (o=="back" || (o=="down" && b>a)) { t=a; a=b; b=t } print a " -> " b }' floor/diag.tsv >> $w/rules_c.txt
  echo "$fam $(m $fam $w/rules.txt $w/floor.txt) $(m $fam $w/rules_c.txt $w/floor.txt) $(m $fam $w/rules.txt $src/laws_served12.txt) $(m $fam $w/rules_c.txt $src/laws_served12.txt)"
done
