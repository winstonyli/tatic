#!/bin/bash
# The one-file-per-section docs (docs/tier-cycle/, docs/related-work/) and their index README.md agree: every file is linked
# once, in sorted order, every link resolves, no file is empty or over 2000 lines (the docs were split to end giant files;
# the largest section is 1518), and no index entry carries a line count (they drifted unchecked; `wc -l` is the count).
# Exit 1 naming the offenders.
cd "${1:-$(dirname "$0")/../..}" || exit 2
fail=0
for dir in docs/tier-cycle docs/related-work; do
  [ -f "$dir/README.md" ] || { echo "missing $dir/README.md (the index)"; fail=1; continue; }
  actual=$(cd $dir && find . -type f -name '*.md' ! -path ./README.md | sed 's|^\./||' | LC_ALL=C sort)
  listed=$(grep -o '](\([^)]*\.md\))' "$dir/README.md" | sed 's/^](//;s/)$//')
  bad=0
  for f in $actual; do [ -s "$dir/$f" ] || { echo "$dir: empty: $f"; bad=1; }; done
  # One process each for the whole directory: a fork per file cost half a minute on Windows.
  over=$(cd $dir && awk 'FNR == 2001 { print FILENAME; nextfile }' $actual </dev/null)
  for f in $over; do echo "$dir: over 2000 lines: $f"; bad=1; done
  unlisted=$(LC_ALL=C comm -23 <(echo "$actual") <(LC_ALL=C sort <<<"$listed"))
  for f in $unlisted; do echo "$dir: not in the index: $f"; bad=1; done
  for f in $listed; do [ -f "$dir/$f" ] || { echo "$dir: dead link in the index: $f"; bad=1; }; done
  counted=$(grep -oE '^- \[[^]]*\]\([^)]*\.md\):.*, [0-9]+ lines' "$dir/README.md" | sed 's/^- \[\([^]]*\)\].*/\1/')
  for f in $counted; do echo "$dir: line count in the index: $f"; bad=1; done
  [ "$actual" == "$listed" ] || [ $bad -eq 1 ] || { echo "$dir: index order differs from file order"; bad=1; }
  [ $bad -eq 0 ] && echo "doc_index_check: $dir: $(wc -l <<<"$actual") files indexed" || fail=1
done
exit $fail
