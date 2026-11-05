#!/usr/bin/env bash
# cite_check_check.sh: cite_check.pl resolves section cites against heading, list and emphasis lines (fixture docs in a temp dir).
here="$(cd "$(dirname "$0")" && pwd)"
t=$(mktemp -d) && trap 'rm -rf "$t"' EXIT
mkdir -p "$t/docs/tier-cycle"
printf '## A heading\n\n*An italic lead-in (2026-01-01, run x).* body\n- **Bold bullet: with colon (note)** more\n' > "$t/docs/tier-cycle/a.md"
fail=0
ok() { [ "$2" = ok ] || { echo "FAIL: $1"; fail=1; }; }
run() { printf '%s\n' "$1" > "$t/PARKED.md"; perl "$here/cite_check.pl" "$t" PARKED.md 2>&1; }
out=$(run 'see `docs/tier-cycle/`, "A heading" and docs/tier-cycle/ section "An italic lead-in" and `docs/tier-cycle/` "Bold bullet: with colon".'); rc=$?
ok "three forms resolve" "$([ $rc = 0 ] && echo "$out" | grep -q '^3 section cites checked, 0 unresolved' && echo ok)"
out=$(run 'see `docs/tier-cycle/`, "No such section".'); rc=$?
ok "a missing section fails and is named" "$([ $rc = 1 ] && echo "$out" | grep -q 'No such section' && echo ok)"
out=$(run 'see `docs/tier-cycle/`, "An italic
  lead-in (2026-01-01, run x)".'); rc=$?
ok "a wrapped title resolves" "$([ $rc = 0 ] && echo ok)"
[ $fail = 0 ] && echo "cite_check_check: ok"
exit $fail
