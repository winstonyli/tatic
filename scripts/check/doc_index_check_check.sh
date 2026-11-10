#!/usr/bin/env bash
# doc_index_check_check.sh: doc_index_check.sh fails on a file left out of the index, a dead link, a file over the limit and a line count in an entry (fixture docs in a temp dir).
here="$(cd "$(dirname "$0")" && pwd)"
t=$(mktemp -d) && trap 'rm -rf "$t"' EXIT
for d in tier-cycle related-work; do
  mkdir -p "$t/docs/$d"; printf 'x\n' > "$t/docs/$d/a.md"; printf '[a](a.md)\n' > "$t/docs/$d/README.md"
done
fail=0
ok() { [ "$2" = ok ] || { echo "FAIL: $1"; fail=1; }; }
run() { bash "$here/doc_index_check.sh" "$t" 2>&1; }
out=$(run); rc=$?
ok "an index that agrees passes" "$([ $rc = 0 ] && echo ok)"
printf 'x\n' > "$t/docs/tier-cycle/b.md"; out=$(run); rc=$?
ok "a file left out of the index fails" "$([ $rc = 1 ] && echo "$out" | grep -q 'not in the index: b.md' && echo ok)"
rm "$t/docs/tier-cycle/b.md"; printf '[c](c.md)\n' >> "$t/docs/related-work/README.md"; out=$(run); rc=$?
ok "a dead link fails" "$([ $rc = 1 ] && echo "$out" | grep -q 'dead link in the index: c.md' && echo ok)"
printf '[a](a.md)\n' > "$t/docs/related-work/README.md"; seq 2000 > "$t/docs/tier-cycle/a.md"; out=$(run); rc=$?
ok "a file at the limit passes" "$([ $rc = 0 ] && echo ok)"
seq 2001 > "$t/docs/tier-cycle/a.md"; out=$(run); rc=$?
ok "a file over the limit fails" "$([ $rc = 1 ] && echo "$out" | grep -q 'over 2000 lines: a.md' && echo ok)"
printf 'x\n' > "$t/docs/tier-cycle/a.md"; printf -- '- [a.md](a.md): A, 1 lines\n' > "$t/docs/tier-cycle/README.md"; out=$(run); rc=$?
ok "an entry with a line count fails" "$([ $rc = 1 ] && echo "$out" | grep -q 'line count in the index: a.md' && echo ok)"
printf -- '- [a.md](a.md): A\n' > "$t/docs/tier-cycle/README.md"; out=$(run); rc=$?
ok "an entry without one passes" "$([ $rc = 0 ] && echo ok)"
[ $fail = 0 ] && echo "doc_index_check_check: ok"
exit $fail
