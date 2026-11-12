#!/bin/bash
# v08-weight-fit.sh: T12's Call-weight fit. Runs the copied test exe (folder v08-fit-exe) 5 times on
# proof::tests::gate::time_call_family, each round followed by time_doubling_12 (the reference, interleaved so both see
# the same machine). headline.txt: per-k medians "k tree build_ms check_ms total_ms", then "doubling12 total_ms" (median).
# Exits non-zero if a run printed no timing line.
set -u
here="$(dirname "$0")"
out="${RUN_DIR:-.}"
for i in 1 2 3 4 5; do
  bash "$here/v08-exe.sh" v08-fit-exe proof::tests::gate::time_call_family --ignored --exact --nocapture > "$out/fit-$i.txt" 2>&1 || { echo "run $i failed" >&2; exit 1; }
  grep -Eq '^[0-9]+ [0-9]+ [0-9.]+ [0-9.]+$' "$out/fit-$i.txt" || { echo "run $i printed no timing line" >&2; exit 1; }
  bash "$here/v08-exe.sh" v08-fit-exe proof::tests::gate::time_doubling_12 --ignored --exact --nocapture > "$out/d12-$i.txt" 2>&1 || { echo "d12 $i failed" >&2; exit 1; }
  grep -q '^build_ms ' "$out/d12-$i.txt" || { echo "d12 $i printed no timing line" >&2; exit 1; }
done
cat "$out"/fit-?.txt | grep -E '^[0-9]+ [0-9]+ [0-9.]+ [0-9.]+$' | sort -n -k1,1 | awk '
  { k=$1; t[k]=$2; n[k]++; b[k,n[k]]=$3; c[k,n[k]]=$4 }
  function med(a,k,m,  i,j,x,v){ for(i=1;i<=m;i++)v[i]=a[k,i]; for(i=1;i<=m;i++)for(j=i+1;j<=m;j++)if(v[j]<v[i]){x=v[i];v[i]=v[j];v[j]=x}; return v[int((m+1)/2)] }
  END { for (k in t) { mb=med(b,k,n[k]); mc=med(c,k,n[k]); printf "%d %d %.1f %.1f %.1f\n", k, t[k], mb, mc, mb+mc } }' | sort -n > "$out/headline.txt"
cat "$out"/d12-?.txt | grep '^build_ms ' | awk '{print $2+$4}' | sort -n | awk '{v[NR]=$1} END {printf "doubling12 %.1f\n", v[int((NR+1)/2)]}' >> "$out/headline.txt"
cat "$out/headline.txt"
