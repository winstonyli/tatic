#!/bin/sh
# per floor law: trace each side alone; "same" if one side's normal form is among the terms the other side's rewriting visited
cd "/c/Users/Winston Li/AppData/Local/Temp/oracle_probe"
for w in $(cut -f2 floor/diag_t.tsv | sort -u); do
  awk -F'\t' -v w=$w '$2==w {split($4,p," = "); print p[1] " = " p[1]; print p[2] " = " p[2]}' floor/diag_t.tsv > $w/sides.txt
  NF_TRACE=1 NF_RULES="$PWD/$w/rules.txt" NF_LAWS="$PWD/$w/sides.txt" ./dose.exe search::normal_forms --exact --ignored --nocapture --test-threads 1 < /dev/null 2>&1 \
  | sed 's/^test search::normal_forms ... //' | awk -v fam=$(echo $w | sed 's/.*tw_s[0-9]*_\([a-z0-9]*\)_.*/\1/') '
    /^TRACE/ { sub(/.*   on /, ""); seen[n] = seen[n] "|" $0 "|"; next }
    /^NF / { r = substr($0, 4); nf[n] = substr(r, 1, index(r, " | ") - 1); n++ }
    END { for (i = 0; i < n; i += 2) { s = index(seen[i], "|" nf[i+1] "|") || index(seen[i+1], "|" nf[i] "|") || nf[i] == nf[i+1]; print fam, s ? "same" : "apart" } }'
done
