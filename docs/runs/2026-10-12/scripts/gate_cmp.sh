# gate_cmp.sh <tag>: compare $TEMP/kk/<tag>_old_<s> with <tag>_new_<s> for salts 1 and 2, with timings and libtest's harness
# lines normalized away; a difference that sorting both files removes is reported as "(order only)"
k=$(cygpath -u "$TEMP")/kk; tag=$1
norm() { case "$(basename $1)" in
  cold.tsv|own.tsv|pooled.tsv) cut -f1-6,8- "$1";; mines.tsv|pooled_prefs.tsv) cut -f1,3- "$1";; m.tsv) cut -f1-4,6- "$1";;
  *.txt|*.log) sed -E "s/[0-9]+(\.[0-9]+)?(s|ms|µs)\b/T/g; s/${tag}_(old|new)/RUN/g; s/[0-9]+ filtered out/N filtered out/; /^running [0-9]+ tests?$/d; /^test .* \.\.\. (ok|FAILED|ignored)$/d; /^test result: /d; /^$/d" "$1";;
  *) cat "$1";; esac; }
for s in 1 2; do o=$k/${tag}_old_$s; n=$k/${tag}_new_$s
  diff <(cd $o && find . -type f | sort) <(cd $n && find . -type f | sort) && echo "salt $s: same file list ($(cd $o && find . -type f | wc -l) files)"
  (cd $o && find . -type f) | while read f; do cmp -s <(norm "$o/$f") <(norm "$n/$f") && continue
    cmp -s <(norm "$o/$f" | sort) <(norm "$n/$f" | sort) && echo "DIFF salt $s $f (order only)" || echo "DIFF salt $s $f"; done
done; echo cmp done
