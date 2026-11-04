#!/bin/bash
# q2_arms_check.sh: q2_arms.sh writes the arms the plan names (dummy exe and weights in a temp dir).
here="$(cd "$(dirname "$0")" && pwd)"
t=$(mktemp -d) && trap 'rm -rf "$t"' EXIT
mkdir "$t/w" && : > "$t/exe" && : > "$t/w/ctx33-v1-s4-10.txt" && : > "$t/w/ctx33-v1-s7-10.txt"
fail=0
ok() { [ "$2" = ok ] || { echo "FAIL: $1"; fail=1; }; }
export WEIGHTS_DIR="$t/w"
bash "$here/q2_arms.sh" "$t/exe" "$t/o" 208 >/dev/null 2>&1 || ok "q2_arms.sh runs" no
e() { cat "$t/o/$1.exe.env" 2>/dev/null; }
ok "c80_4-10 selects ctx" "$(e c80_4-10 | grep -qx 'EXTRAS_SELECT=ctx' && echo ok)"
ok "c80_4-10 names weights without a space" "$(e c80_4-10 | grep -E '^CTX_WEIGHTS=[^ ]*ctx33-v1-s4-10.txt$' >/dev/null && echo ok)"
ok "c160_7-10_d4 has GEN_DRAW=4 and weights s7-10" "$(e c160_7-10_d4 | grep -qx 'GEN_DRAW=4' && e c160_7-10_d4 | grep -q 's7-10.txt' && echo ok)"
ok "r208_d3 is EXTRAS_N=208 and GEN_DRAW=3" "$(e r208_d3 | grep -qx 'EXTRAS_N=208' && e r208_d3 | grep -qx 'GEN_DRAW=3' && ! e r208_d3 | grep -q POOL && echo ok)"
ok "s80_d0 has no GEN_DRAW" "$(! e s80_d0 | grep -q GEN_DRAW && e s80_d0 | grep -qx 'EXTRAS_SELECT=small' && e s80_d0 | grep -qx 'POOL=4' && echo ok)"
ok "ctx draw 0 has no GEN_DRAW" "$(! e c80_7-10 | grep -q GEN_DRAW && echo ok)"
ok "every arm has its exe" "$([ -f "$t/o/c160_4-10_d3.exe" ] && [ -f "$t/o/r208_d4.exe" ] && echo ok)"
ok "arm count: 6 s + 12 c + 3 r" "$([ "$(ls "$t/o"/*.exe | wc -l)" = 21 ] && echo ok)"
rm "$t/w/ctx33-v1-s7-10.txt"
bash "$here/q2_arms.sh" "$t/exe" "$t/o2" >/dev/null 2>&1 && ok "a missing weights file fails" no
[ $fail = 0 ] && echo "q2_arms_check: ok"
exit $fail
