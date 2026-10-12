# usage: sumrows.sh dir...  -> per dir: total M of each stage tsv, and pooled per family
for d in "$@"; do line="$(basename $d):"
  for st in mines own cold pooled; do f=$d/$st.tsv; [ -f $f ] || continue
    if [ $st = mines ]; then m=$(awk -F'\t' '{s+=$3} END{print s}' $f); else m=$(awk -F'\t' '{s+=$4} END{print s}' $f); fi
    line="$line $st=$m"; done
  echo "$line"; done
