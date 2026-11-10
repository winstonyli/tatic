#!/usr/bin/env bash
# stack_literal_check_check.sh: stack_literal_check.sh passes the named constant and other sizes, and fails on each spelling of 256 MB (throwaway git repo).
here="$(cd "$(dirname "$0")" && pwd)"
t=$(mktemp -d) && trap 'rm -rf "$t"' EXIT
mkdir -p "$t/scripts/check" "$t/crates/a/src/deep" "$t/docs" && cp "$here/stack_literal_check.sh" "$t/scripts/check/"
cd "$t" && git init -q . && git config user.email a@b && git config user.name t
f=crates/a/src/deep/x.rs
printf 'b.stack_size(tatic_kernel::CHECK_STACK);\nb.stack_size(2 << 20);\nb.stack_size(1256 << 200);\n' > crates/a/src/lib.rs; printf 'a 256 << 20 stack\n' > docs/a.md
git add -A && git commit -qm x
fail=0
want() { # <case> <rc> <grep text>
  out=$(bash scripts/check/stack_literal_check.sh .); rc=$?
  { [ $rc = "$2" ] && echo "$out" | grep -q "$3"; } || { echo "FAIL: $1 (rc=$rc)"; echo "$out"; fail=1; }
}
want "the constant, other sizes and docs pass" 0 'ok'
for lit in '256 << 20' '256<<20' '256 * 1024 * 1024' '268435456' '268_435_456'; do
  printf 'b.stack_size(%s);\n' "$lit" > $f; git add -A; want "$lit fails" 1 "x.rs:1:"
done
printf 'b.stack_size(256 << 20);\n' > $f; git add -A; git rm -q --cached $f; want "an untracked file is not read" 0 'ok'
[ $fail = 0 ] && echo "stack_literal_check_check: ok"
exit $fail
