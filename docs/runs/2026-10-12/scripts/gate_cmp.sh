# gate_cmp.sh <tag>: compare $TEMP/kk/<tag>_old_<s> with <tag>_new_<s> for salts 1 and 2, timings normalized
k=$(cygpath -u "$TEMP")/kk; tag=$1
norm() { case "$(basename $1)" in
  cold.tsv|own.tsv|pooled.tsv) cut -f1-6,8- "$1";; mines.tsv) cut -f1,3- "$1";;
  *.txt|*.log) sed -E "s/[0-9]+(\.[0-9]+)?(s|ms|µs)\b/T/g; s/${tag}_(old|new)/RUN/g; s/[0-9]+ filtered out/N filtered out/" "$1";;
  *) cat "$1";; esac; }
for s in 1 2; do o=$k/${tag}_old_$s; n=$k/${tag}_new_$s
  diff <(cd $o && find . -type f | sort) <(cd $n && find . -type f | sort) && echo "salt $s: same file list ($(cd $o && find . -type f | wc -l) files)"
  (cd $o && find . -type f) | while read f; do cmp -s <(norm "$o/$f") <(norm "$n/$f") || echo "DIFF salt $s $f"; done
done; echo cmp done
