# gate_cmp.sh <tag>: compare <run dir, kk.sh>/<tag>_old_<s> with <tag>_new_<s> for salts 1 and 2, with timings and libtest's harness
# lines normalized away; a difference that sorting both files removes is reported as "(order only)"
k=$(bash "$(dirname "$0")/kk.sh"); tag=$1
norm() { case "$(basename $1)" in
  cold.tsv|own.tsv|pooled.tsv) cut -f1-6,8- "$1";; mines.tsv|pooled_prefs.tsv) cut -f1,3- "$1";; m.tsv) cut -f1-4,6- "$1";;
  *.txt|*.log) sed -E "s/[0-9]+(\.[0-9]+)?(s|ms|µs)\b/T/g; s/${tag}_(old|new)/RUN/g; s/[0-9]+ filtered out/N filtered out/; /^running [0-9]+ tests?$/d; /^test .* \.\.\. (ok|FAILED|ignored)$/d; /^test result: /d; /^$/d" "$1";;
  *) cat "$1";; esac; }
# Normalized copies go to files, not process substitutions: under load a substitution once failed silently and its empty
# stream showed as a difference (2026-10-16, a byte-identical file reported "order only"). A failed step says ERROR.
t=$(mktemp -d); trap 'rm -rf "$t"' EXIT
nm() { norm "$1" > "$2" || { echo "ERROR salt $s: normalizing $1 failed"; return 1; }; }
for s in 1 2; do o=$k/${tag}_old_$s; n=$k/${tag}_new_$s
  (cd $o && find . -type f | sort) > $t/lo && (cd $n && find . -type f | sort) > $t/ln || { echo "ERROR salt $s: listing failed"; continue; }
  diff $t/lo $t/ln && echo "salt $s: same file list ($(wc -l < $t/lo) files)"
  while read f; do nm "$o/$f" $t/o && nm "$n/$f" $t/n || continue
    cmp -s $t/o $t/n && continue
    sort $t/o > $t/os && sort $t/n > $t/ns || { echo "ERROR salt $s: sorting $f failed"; continue; }
    cmp -s $t/os $t/ns && echo "DIFF salt $s $f (order only)" || echo "DIFF salt $s $f"; done < $t/lo
done; echo cmp done
