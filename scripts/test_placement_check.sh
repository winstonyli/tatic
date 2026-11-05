#!/usr/bin/env bash
# test_placement_check.sh [root]: no tracked .rs file holds an inline top-level `mod tests { ... }` (or `mod *_tests`) block of
# LIMIT lines or more; that block goes to `foo/tests.rs` (`foo/tests/` once it splits). Exit 1 listing the offenders.
cd "${1:-$(dirname "$0")/..}" || exit 2
LIMIT=300
out=$(git ls-files '*.rs' | tr -d '\r' | xargs awk -v lim=$LIMIT '
  FNR == 1 { open = 0 }
  /^mod [A-Za-z_]*tests? *\{/ { open = FNR; name = $2 }
  open && /^\}/ { n = FNR - open + 1; if (n >= lim) printf "inline test block of %d lines: %s `%s` (line %d); move it to a tests.rs\n", n, FILENAME, name, open; open = 0 }
')
[ -z "$out" ] && { echo "test_placement_check: ok"; exit 0; }
echo "$out"; exit 1
