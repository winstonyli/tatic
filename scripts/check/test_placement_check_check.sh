#!/usr/bin/env bash
# test_placement_check_check.sh: test_placement_check.sh passes a tidy tree and fails on a long inline test block (throwaway git repo).
here="$(cd "$(dirname "$0")" && pwd)"
t=$(mktemp -d) && trap 'rm -rf "$t"' EXIT
mkdir -p "$t/scripts/check" && cp "$here/test_placement_check.sh" "$t/scripts/check/"
cd "$t" && git init -q . && git config user.email a@b && git config user.name t
blk() { printf 'fn f() {}\n#[cfg(test)]\nmod %s {\n' "$1"; seq 1 "$2" | sed 's/^/    \/\/ /'; printf '}\n'; }
blk tests 100 > small.rs; blk tests 297 > edge.rs
git add -A && git commit -qm x
fail=0
want() { # <case> <rc> <grep text>
  out=$(bash scripts/check/test_placement_check.sh .); rc=$?
  { [ $rc = "$2" ] && echo "$out" | grep -q "$3"; } || { echo "FAIL: $1 (rc=$rc)"; echo "$out"; fail=1; }
}
want "short blocks pass" 0 'ok'
blk tests 298 > edge.rs; git add -A; want "a block of exactly 300 lines fails" 1 'edge.rs'
blk stats_tests 400 > edge.rs; git add -A; want "a long mod *_tests block fails" 1 'stats_tests'
blk tests 400 | sed 's/^mod /    mod /;s/^}/    }/' > edge.rs; git add -A; want "a nested block is not top-level" 0 'ok'
[ $fail = 0 ] && echo "test_placement_check_check: ok"
exit $fail
