#!/bin/bash
# The one-file-per-section docs (docs/tier-cycle/, docs/related-work/) and their index README.md agree: every file is linked
# once, in sorted order, every link resolves, no file is empty. Exit 1 naming the offenders.
cd "$(dirname "$0")/../.." || exit 2
fail=0
for dir in docs/tier-cycle docs/related-work; do
  [ -f "$dir/README.md" ] || { echo "missing $dir/README.md (the index)"; fail=1; continue; }
  actual=$(cd $dir && find . -type f -name '*.md' ! -path ./README.md | sed 's|^\./||' | LC_ALL=C sort)
  listed=$(grep -o '](\([^)]*\.md\))' "$dir/README.md" | sed 's/^](//;s/)$//')
  bad=0
  for f in $actual; do [ -s "$dir/$f" ] || { echo "$dir: empty: $f"; bad=1; }; done
  for f in $actual; do grep -qxF "$f" <<<"$listed" || { echo "$dir: not in the index: $f"; bad=1; }; done
  for f in $listed; do [ -f "$dir/$f" ] || { echo "$dir: dead link in the index: $f"; bad=1; }; done
  [ "$actual" == "$listed" ] || [ $bad -eq 1 ] || { echo "$dir: index order differs from file order"; bad=1; }
  [ $bad -eq 0 ] && echo "doc_index_check: $dir: $(wc -l <<<"$actual") files indexed" || fail=1
done
exit $fail
