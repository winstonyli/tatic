# same_arms.sh <dir a> <dir b>: whether two sweeps agree, time columns aside: every stage's .tsv without its seconds
# column (column 2 in mines*.tsv and pooled_prefs.tsv, 7 in the loop stages'), and every loop's and mine's rules.txt.
# Prints "same" or each differing file.
a=$(cygpath -u "$1"); b=$(cygpath -u "$2"); bad=0  # Unix form: a backslash in a pattern below is an escape
for t in "$a"/*.tsv; do
  n=${t#"$a"/}
  case $n in mines*|pooled_prefs*) c="-f1,3-" ;; *) c="-f1-6,8-" ;; esac
  cmp -s <(cut $c "$t") <(cut $c "$b/$n" 2>/dev/null) || { echo "$n"; bad=1; }
done
for r in "$a"/*/rules.txt; do
  l=${r#"$a"/}; cmp -s "$r" "$b/$l" || { echo "$l"; bad=1; }
done
[ $bad = 0 ] && echo same
