#!/usr/bin/env bash
# size_check_check.sh: size_check.sh passes a tidy tree and fails on each way of drifting (a throwaway git repo in a temp dir).
here="$(cd "$(dirname "$0")" && pwd)"
t=$(mktemp -d) && trap 'rm -rf "$t"' EXIT
mkdir -p "$t/scripts" && cp "$here/size_check.sh" "$t/scripts/"
cd "$t" && git init -q . && git config user.email a@b && git config user.name t
seq 1 1500 > big.rs; seq 1 10 > small.rs; seq 1 1200 > other.rs
printf 'big.rs 1500\n' > scripts/size_allowlist.txt
git add -A && git commit -qm x
fail=0
want() { # <case> <rc> <grep text>
  out=$(bash scripts/size_check.sh .); rc=$?
  { [ $rc = "$2" ] && echo "$out" | grep -q "$3"; } || { echo "FAIL: $1 (rc=$rc)"; echo "$out"; fail=1; }
}
want "an unlisted big file fails" 1 'not listed: other.rs'
printf 'big.rs 1500\nother.rs 1200\n' > scripts/size_allowlist.txt; want "a tidy tree passes" 0 'ok'
seq 1 1501 > big.rs; git add -A; want "growth fails" 1 'grew past its max: big.rs'
seq 1 1400 > big.rs; git add -A; want "shrinking without lowering fails" 1 'lower its max to 1400'
seq 1 900 > big.rs; git add -A; want "a listed file under the limit fails" 1 'delete its line'
printf 'big.rs 900\ngone.rs 1100\nother.rs 1200\n' > scripts/size_allowlist.txt; want "a listed untracked file fails" 1 'not tracked: gone.rs'
[ $fail = 0 ] && echo "size_check_check: ok"
exit $fail
