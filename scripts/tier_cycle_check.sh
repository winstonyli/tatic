#!/bin/bash
# The findings log docs/tier-cycle/ and its index README.md agree: every file is linked once, in sorted order,
# every link resolves, no file is empty. Exit 1 naming the offenders.
cd "$(dirname "$0")/.." || exit 2
dir=docs/tier-cycle
fail=0
[ -f "$dir/README.md" ] || { echo "missing $dir/README.md (the index)"; exit 1; }
actual=$(cd $dir && find . -type f -name '*.md' ! -path ./README.md | sed 's|^\./||' | LC_ALL=C sort)
listed=$(grep -o '](\([^)]*\.md\))' "$dir/README.md" | sed 's/^](//;s/)$//')
for f in $actual; do [ -s "$dir/$f" ] || { echo "empty: $f"; fail=1; }; done
for f in $actual; do grep -qxF "$f" <<<"$listed" || { echo "not in the index: $f"; fail=1; }; done
for f in $listed; do [ -f "$dir/$f" ] || { echo "dead link in the index: $f"; fail=1; }; done
[ "$actual" == "$listed" ] || [ $fail -eq 1 ] || { echo "index order differs from file order"; fail=1; }
[ $fail -eq 0 ] && echo "tier_cycle_check: $(wc -l <<<"$actual") files indexed"
exit $fail
