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
mkdir -p "$t/docs/related-work"; printf '## 9. x\n' > "$t/docs/related-work/09-x.md"; printf '## 12. y\n' > "$t/docs/related-work/12-y.md"
out=$(run 'see `docs/related-work/` §9 and §12, and §12 of `docs/related-work/`.'); rc=$?
ok "§ cites resolve to numbered files, in both orders" "$([ $rc = 0 ] && echo "$out" | grep -q '^3 section cites checked, 0 unresolved' && echo ok)"
out=$(run 'see `docs/related-work/` §9 and §13.'); rc=$?
ok "a § with no file fails and is named" "$([ $rc = 1 ] && echo "$out" | grep -q '§13' && echo ok)"
out=$(run 'see `docs/related-work/` section 9, sections 9 and 12, `docs/related-work/` 12 and docs/related-work/ sec 9.'); rc=$?
ok "section N, sec N and bare numbers resolve" "$([ $rc = 0 ] && echo "$out" | grep -q '^5 section cites checked, 0 unresolved' && echo ok)"
out=$(run 'see `docs/related-work/` section 13.'); rc=$?
ok "a section N with no file fails" "$([ $rc = 1 ] && echo "$out" | grep -q '§13' && echo ok)"
out=$(run 'see `docs/tier-cycle/`, “No such section”.'); rc=$?
ok "a curly-quoted title is read" "$([ $rc = 1 ] && echo "$out" | grep -q 'No such section' && echo ok)"
long=$(printf 'x%.0s' {1..120}); printf '## %s\n' "$long" >> "$t/docs/tier-cycle/a.md"
out=$(run "see docs/tier-cycle/, \"$long\"."); rc=$?
ok "a long title is read" "$([ $rc = 0 ] && echo "$out" | grep -q '^1 section cites checked' && echo ok)"
mkdir -p "$t/crates"; rs() { printf '%s\n' "$1" > "$t/crates/x.rs"; perl "$here/cite_check.pl" "$t" crates/x.rs 2>&1; }
out=$(rs '/// see `docs/related-work/`
/// section 9, and `docs/tier-cycle/`,
/// "A heading".'); rc=$?
ok "a cite wrapped in a code comment resolves" "$([ $rc = 0 ] && echo "$out" | grep -q '^2 section cites checked, 0 unresolved' && echo ok)"
out=$(rs "// see docs/related-work/'s own discussion."); rc=$?
ok "a code cite with no section fails" "$([ $rc = 1 ] && echo "$out" | grep -q 'no section' && echo ok)"
out=$(rs 'let p = "docs/tier-cycle/"; // see `docs/tier-cycle/` ("A heading").'); rc=$?
ok "a code string is not a cite, a parenthesised title is" "$([ $rc = 0 ] && echo "$out" | grep -q '^1 section cites checked, 0 unresolved' && echo ok)"
out=$(run 'findings are in `docs/related-work/`.'); rc=$?
ok "a doc naming a directory with no section fails" "$([ $rc = 1 ] && echo "$out" | grep -q 'no section' && echo ok)"
out=$(run 'the index is `docs/related-work/README.md`, a TOUR cite `docs/tier-cycle/#A heading`.'); rc=$?
ok "the index and a TOUR cite pass" "$([ $rc = 0 ] && echo ok)"
cm() { printf '%s\n' "$2" > "$t/$1"; perl "$here/cite_check.pl" "$t" "$1" 2>&1; }
out=$(cm x.sh '# see docs/tier-cycle/, "No such section".'); rc=$?
ok "a shell comment is read" "$([ $rc = 1 ] && echo "$out" | grep -q 'No such section' && echo ok)"
out=$(cm x.toml '# see docs/tier-cycle/, "A heading".
p = "docs/tier-cycle/"'); rc=$?
ok "a toml comment is read, its strings are not" "$([ $rc = 0 ] && echo "$out" | grep -q '^1 section cites checked, 0 unresolved' && echo ok)"
out=$(cm x.sh '# see docs/tier-cycle.md, "A heading".'); rc=$?
ok "a long doc's old name fails" "$([ $rc = 1 ] && echo "$out" | grep -q 'old name' && echo ok)"
out=$(run 'see `docs/tier-cycle/`, "A hea".'); rc=$?
ok "a title cut mid-word fails" "$([ $rc = 1 ] && echo ok)"
out=$(run 'see `docs/tier-cycle/`, "A heading and a stray quote
then docs/tier-cycle/ bare, and much later on '"$long$long"' a "tail'); rc=$?
ok "an unclosed quote does not swallow what follows" "$([ $rc = 1 ] && [ "$(echo "$out" | grep -c 'no section')" = 2 ] && echo ok)"
rm -f "$t"/x.sh "$t"/x.toml "$t"/crates/x.rs; mkdir -p "$t/docs/runs" "$t/docs/superpowers" "$t/scripts/check"
for f in docs/runs/r.md docs/runs.md docs/superpowers/s.md scripts/check/c.sh; do printf '# in docs/tier-cycle/ somewhere\n' > "$t/$f"; done
printf 'in `docs/tier-cycle/`, "A heading".\n' > "$t/PARKED.md"; printf 'in docs/tier-cycle/ alone\n' > "$t/new.md"
git -C "$t" init -q . && git -C "$t" add -A 2>/dev/null
out=$(perl "$here/cite_check.pl" "$t" 2>&1); rc=$?
ok "by default every tracked doc is read but the history and the guards" "$([ $rc = 1 ] && echo "$out" | grep -q '^new.md: docs/tier-cycle/ with no section' && [ "$(echo "$out" | grep -c 'no section')" = 1 ] && echo ok)"
[ $fail = 0 ] && echo "cite_check_check: ok"
exit $fail
