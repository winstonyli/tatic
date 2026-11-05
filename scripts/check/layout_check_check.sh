#!/usr/bin/env bash
# layout_check_check.sh: layout_check.sh passes files in role directories and fails on one directly in scripts/ (throwaway git repo).
here="$(cd "$(dirname "$0")" && pwd)"
t=$(mktemp -d) && trap 'rm -rf "$t"' EXIT
mkdir -p "$t/scripts/check" "$t/scripts/gate" && cp "$here/layout_check.sh" "$t/scripts/check/"
cd "$t" && git init -q . && git config user.email a@b && git config user.name t
touch scripts/gate/a.sh
git add -A && git commit -qm x
fail=0
want() { # <case> <rc> <grep text>
  out=$(bash scripts/check/layout_check.sh .); rc=$?
  { [ $rc = "$2" ] && echo "$out" | grep -q "$3"; } || { echo "FAIL: $1 (rc=$rc)"; echo "$out"; fail=1; }
}
want "role directories pass" 0 'ok'
touch scripts/loose.sh; git add -A; want "a file directly in scripts/ fails" 1 'loose.sh'
[ $fail = 0 ] && echo "layout_check_check: ok"
exit $fail
