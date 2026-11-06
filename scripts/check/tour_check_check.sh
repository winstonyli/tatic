#!/usr/bin/env bash
# tour_check_check.sh: tour_check.sh passes a cite that resolves and fails on a missing path and a missing symbol (fixture tour in a temp dir).
here="$(cd "$(dirname "$0")" && pwd)"
t=$(mktemp -d) && trap 'rm -rf "$t"' EXIT
mkdir -p "$t/docs" "$t/src/m"; printf 'fn real() {}\n' > "$t/src/m/a.rs"
fail=0
ok() { [ "$2" = ok ] || { echo "FAIL: $1"; fail=1; }; }
run() { bash "$here/tour_check.sh" "$t" 2>&1; }
printf '`src/m/a.rs#real` and `src/m#real`\n' > "$t/docs/TOUR.md"; out=$(run); rc=$?
ok "a file cite and a directory cite that resolve pass" "$([ $rc = 0 ] && echo "$out" | grep -q '2 cites checked, 0 broken' && echo ok)"
printf '`src/m/b.rs#real`\n' > "$t/docs/TOUR.md"; out=$(run); rc=$?
ok "a missing path fails" "$([ $rc = 1 ] && echo "$out" | grep -q 'missing path: src/m/b.rs#real' && echo ok)"
printf '`src/m/a.rs#gone`\n' > "$t/docs/TOUR.md"; out=$(run); rc=$?
ok "a missing symbol fails" "$([ $rc = 1 ] && echo "$out" | grep -q 'missing symbol: src/m/a.rs#gone' && echo ok)"
[ $fail = 0 ] && echo "tour_check_check: ok"
exit $fail
