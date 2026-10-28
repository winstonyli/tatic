#!/bin/bash
# stack_names.sh <samples file> <exe>: names stack_sample.ps1's samples with llvm-symbolizer against <exe>'s PDB (image
# base 0x140000000, inlined frames expanded; a word outside any function names as ??). Prints the rips' functions by
# count, then each function's count of samples whose stack words reach it (recurring frames are the real ones; a
# recursion shows as one function repeated), then the last sample's distinct frames innermost first, as runs of repeats.
f=$1; exe=$2; t=$(mktemp -d)
grep -o '[0-9a-f]\+' <(sed 's/^rip \|^stack //' "$f") | sort -u > "$t/rvas"
awk '{ printf "0x%x\n", strtonum("0x" $1) + 0x140000000 }' "$t/rvas" | llvm-symbolizer --obj="$exe" --functions=linkage --demangle --inlining > "$t/out"
# rva -> innermost name ; outermost name (blank-line separated blocks, 2 lines per frame)
awk -v RS= -F'\n' '{ print $1 "\t" $(NF-1) }' "$t/out" | sed -E 's/::h[0-9a-f]{16}//g' > "$t/names"
paste "$t/rvas" "$t/names" > "$t/map"
echo "== rip functions (innermost frame), by samples"
grep '^rip ' "$f" | awk '{print $2}' | awk -F'\t' 'NR==FNR { n[$1]=$2; next } { print n[$1] }' "$t/map" - | sort | uniq -c | sort -rn | head -8
echo "== functions reached from the stack words (outermost inlined frame), samples containing them"
grep '^stack ' "$f" | awk -F'\t' 'NR==FNR { n[$1]=$3; next } { delete s; for (i = 2; i <= NF; i++) ; } { split($0, w, " "); for (i = 2; i in w; i++) if (n[w[i]] != "" && n[w[i]] != "??") s[n[w[i]]] = 1; for (k in s) c[k]++ } END { for (k in c) print c[k] "\t" k }' "$t/map" - | sort -rn | head -40
echo "== last sample's frames, innermost first (runs of a repeated frame collapsed)"
tail -1 "$f" | tr ' ' '\n' | tail -n +2 | awk -F'\t' 'NR==FNR { n[$1]=$3; next } n[$1] != "" && n[$1] != "??" { print n[$1] }' "$t/map" - | uniq -c | head -60
rm -rf "$t"
