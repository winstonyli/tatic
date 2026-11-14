#!/usr/bin/env bash
# path_cite_check_check.sh: path_cite_check.pl fails on a backticked repo path that does not exist, unless a gone-word marks it (fixtures in a temp dir).
here="$(cd "$(dirname "$0")" && pwd)"
t=$(mktemp -d) && trap 'rm -rf "$t"' EXIT
mkdir -p "$t/crates/a/src" "$t/scripts/study" && : > "$t/crates/a/src/lib.rs" && : > "$t/scripts/study/x.sh"
fail=0
ok() { [ "$2" = ok ] || { echo "FAIL: $1"; fail=1; }; }
run() { printf '%s\n' "$1" > "$t/NOTES.md"; perl "$here/path_cite_check.pl" "$t" NOTES.md 2>&1; }
out=$(run 'see `crates/a/src/lib.rs#parse`, `crates/a/src/lib.rs:12`, `crates/a/src/` and `scripts/study/x.sh`.'); rc=$?
ok "existing paths with suffixes pass" "$([ $rc = 0 ] && echo "$out" | grep -q '^4 path cites checked, 0 broken' && echo ok)"
out=$(run 'see `scripts/gone.sh`.'); rc=$?
ok "a missing path fails and is named" "$([ $rc = 1 ] && echo "$out" | grep -q 'scripts/gone.sh' && echo ok)"
out=$(run 'see `scripts/gone.sh` (deleted in abc1234).'); rc=$?
ok "a path marked deleted is skipped" "$([ $rc = 0 ] && echo "$out" | grep -q '^0 path cites checked' && echo ok)"
out=$(run 'it was removed:
`scripts/gone.sh` held the loop.'); rc=$?
ok "a gone-word on the line before counts" "$([ $rc = 0 ] && echo ok)"
out=$(run 'globs `scripts/*.sh`, templates `docs/runs/<date>/` and `crates/{a,b}` name no file.'); rc=$?
ok "globs and placeholders are skipped" "$([ $rc = 0 ] && echo "$out" | grep -q '^0 path cites checked' && echo ok)"
out=$(run 'a sentence ending in `crates/a/src/lib.rs`, and `crates/a/src/lib.rs`.'); rc=$?
ok "trailing punctuation inside the backticks is dropped" "$([ $rc = 0 ] && echo ok)"
out=$(run 'plain scripts/gone.sh outside backticks is prose.'); rc=$?
ok "an unquoted path is not a cite" "$([ $rc = 0 ] && echo ok)"
mkdir -p "$t/docs/runs" "$t/docs/superpowers" "$t/scripts/check"
for f in docs/runs/r.md docs/runs.md docs/superpowers/s.md scripts/check/c.sh; do printf 'see `scripts/gone.sh`\n' > "$t/$f"; done
printf 'see `scripts/study/x.sh`\n' > "$t/NOTES.md"
git -C "$t" init -q . && git -C "$t" add -A 2>/dev/null
out=$(perl "$here/path_cite_check.pl" "$t" 2>&1); rc=$?
ok "the history and the guards are not scanned" "$([ $rc = 0 ] && echo "$out" | grep -q '^1 path cites checked, 0 broken' && echo ok)"
printf 'see `scripts/gone.sh`\n' > "$t/new.md"; git -C "$t" add new.md
out=$(perl "$here/path_cite_check.pl" "$t" 2>&1); rc=$?
ok "a tracked doc is scanned by default" "$([ $rc = 1 ] && echo "$out" | grep -q 'new.md' && echo ok)"
[ $fail = 0 ] && echo "path_cite_check_check: ok"
exit $fail
