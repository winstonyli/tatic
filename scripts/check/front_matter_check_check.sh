#!/usr/bin/env bash
# front_matter_check_check.sh: front_matter_check.sh passes each allowed status and fails on none, a bad one or a missing successor (throwaway git repo).
here="$(cd "$(dirname "$0")" && pwd)"
t=$(mktemp -d) && trap 'rm -rf "$t"' EXIT
mkdir -p "$t/scripts/check" "$t/docs/superpowers/specs" "$t/docs/superpowers/plans" && cp "$here/front_matter_check.sh" "$t/scripts/check/"
cd "$t" && git init -q . && git config user.email a@b && git config user.name t
d=docs/superpowers
printf -- '---\nstatus: draft\n---\n# a\n' > $d/specs/a.md; printf -- '---\r\nstatus: done\r\n---\r\n# b\r\n' > $d/plans/b.md
printf -- '---\nstatus: "superseded-by: a.md"\n---\n# c\n' > $d/specs/c.md; printf '# not a spec\n' > $d/README.md
git add -A && git commit -qm x
fail=0
want() { # <case> <rc> <grep text>
  out=$(bash scripts/check/front_matter_check.sh .); rc=$?
  { [ $rc = "$2" ] && echo "$out" | grep -q "$3"; } || { echo "FAIL: $1 (rc=$rc)"; echo "$out"; fail=1; }
}
want "allowed statuses and CRLF pass, other files are not read" 0 'ok'
printf '# d\n' > $d/plans/d.md; git add -A; want "no front matter fails" 1 'd.md: no front matter'
rm $d/plans/d.md; printf -- '---\nstatus: parked\n---\n' > $d/plans/e.md; git add -A; want "a bad status fails" 1 'e.md: bad status: parked'
rm $d/plans/e.md; printf -- '---\ntitle: x\n---\nstatus: done\n' > $d/plans/f.md; git add -A; want "a status below the front matter fails" 1 'f.md: bad status: none'
rm $d/plans/f.md; printf -- '---
---
status: done
' > $d/plans/f.md; git add -A; want "empty front matter does not read the body" 1 'f.md: bad status: none'
rm $d/plans/f.md; printf -- '---
status: done
# no close
' > $d/plans/f.md; git add -A; want "unclosed front matter fails" 1 'f.md: bad status: none'
rm $d/plans/f.md; printf -- '---\nstatus: "superseded-by: gone.md"\n---\n' > $d/specs/g.md; git add -A; want "a missing successor fails" 1 'g.md: superseded by a missing file'
[ $fail = 0 ] && echo "front_matter_check_check: ok"
exit $fail
