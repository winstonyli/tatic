#!/usr/bin/env bash
# script_header_check_check.sh: script_header_check.sh passes scripts with a header and fails on one without (throwaway git repo).
here="$(cd "$(dirname "$0")" && pwd)"
t=$(mktemp -d) && trap 'rm -rf "$t"' EXIT
mkdir -p "$t/scripts/check" "$t/docs/runs/2026-01-01/scripts" && cp "$here/script_header_check.sh" "$t/scripts/check/"
cd "$t" && git init -q . && git config user.email a@b && git config user.name t
d=docs/runs/2026-01-01/scripts
printf '#!/bin/bash\n# a.sh: does a thing\nx\n' > $d/a.sh; printf '"""b.py: does b"""\nx\n' > $d/b.py; printf 'x\n' > $d/data.txt
git add -A && git commit -qm x
fail=0
want() { # <case> <rc> <grep text>
  out=$(bash scripts/check/script_header_check.sh .); rc=$?
  { [ $rc = "$2" ] && echo "$out" | grep -q "$3"; } || { echo "FAIL: $1 (rc=$rc)"; echo "$out"; fail=1; }
}
want "a comment and a docstring pass, data files are not scripts" 0 'ok'
printf '#!/bin/bash\nx\n' > $d/c.sh; git add -A; want "a shebang alone is no header" 1 'c.sh'
[ $fail = 0 ] && echo "script_header_check_check: ok"
exit $fail
