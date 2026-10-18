# same_arms.sh <dir a> <dir b>: whether two sweeps' cold stages agree, time columns aside: cold.tsv without column 7
# (seconds), and every loop's rules.txt. Prints "same" or each differing file.
a=$(cygpath -u "$1"); b=$(cygpath -u "$2"); bad=0  # Unix form: a backslash in a pattern below is an escape
cmp -s <(cut -f1-6,8- "$a/cold.tsv") <(cut -f1-6,8- "$b/cold.tsv") || { echo "cold.tsv"; bad=1; }
for r in "$a"/cold_*/rules.txt; do
  l=${r#"$a"/}; cmp -s "$r" "$b/$l" || { echo "$l"; bad=1; }
done
[ $bad = 0 ] && echo same
