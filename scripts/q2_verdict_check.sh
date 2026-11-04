#!/bin/bash
# q2_verdict_check.sh: q2_verdict.sh applies the pre-registered Q2 rule to streams_ab.sh logs (fixture logs inline).
here="$(cd "$(dirname "$0")" && pwd)"
t=$(mktemp -d) && trap 'rm -rf "$t"' EXIT
fail=0
ok() { [ "$2" = ok ] || { echo "FAIL: $1"; fail=1; }; }
# log <file> <H_A> <W_A> <H_B> <W_B> [<last line>]: the lines of a gate that the rule reads
log() {
  {
    echo "salt 1: M A 100 B 99; held A 1 B 1"
    echo "total A: M 5; held $2; wall 1 s, job cpu 2 s; memo peak 3 terms; peakproc max 4; work interp=0 walk=$3 match=7 op=8"
    echo "total B: M 5; held $4; wall 1 s, job cpu 2 s; memo peak 3 terms; peakproc max 4; work interp=0 walk=$5 match=7 op=8"
    echo "${6:-streams_ab: rules same in 0 of 3 loops; 0 of 6 arms failed}"
  } > "$1"
}
v() { bash "$here/q2_verdict.sh" "$@" 2>&1; }
log "$t/pass" 5000 100 4800 104
log "$t/d3" 5030 0 0 0
log "$t/d4" 5050 0 0 0
out=$(v lab "$t/pass" "$t/d3" "$t/d4"); rc=$?
ok "pass fixture exits 0" "$([ $rc = 0 ] && echo ok)"
ok "pass line" "$([ "$out" = "lab: small 5000 walk 100; ctx 4800 walk 104; spread 50; threshold 76; held diff -200; work ratio 1.040; PASS" ] && echo ok)"
log "$t/held" 5000 100 4950 104
ok "held-out fail" "$(v lab "$t/held" "$t/d3" "$t/d4" | grep -q 'held diff -50; .*FAIL' && echo ok)"
log "$t/work" 5000 100 4800 106
ok "work fail" "$(v lab "$t/work" "$t/d3" "$t/d4" | grep -q 'work ratio 1.060; FAIL' && echo ok)"
log "$t/s90" 5000 100 4920 104
log "$t/d3b" 5090 0 0 0
ok "spread 90 lifts the threshold: D -80 fails" "$(v lab "$t/s90" "$t/d3b" "$t/d4" | grep -q 'spread 90; threshold 90; held diff -80; .*FAIL' && echo ok)"
log "$t/bad" 5000 100 4800 104 "streams_ab: rules same in 0 of 3 loops; 2 of 6 arms failed"
out=$(v lab "$t/bad" "$t/d3" "$t/d4"); rc=$?
ok "a failed arm exits 2 with no verdict line" "$([ $rc = 2 ] && ! echo "$out" | grep -qE 'PASS|FAIL$' && echo ok)"
log "$t/few" 5000 100 4800 104 "streams_ab: rules same in 0 of 3 loops; 0 of 2 arms failed"
out=$(v lab "$t/pass" "$t/few" "$t/d4"); rc=$?
ok "mismatched arm counts exit 2" "$([ $rc = 2 ] && ! echo "$out" | grep -qE 'PASS|FAIL$' && echo ok)"
ok "--d-only, T 76: yes" "$(v --d-only lab "$t/pass" 76 | grep -qx 'lab: D -200; work ratio 1.040; D < -T: yes' && echo ok)"
ok "--d-only, T 250: no" "$(v --d-only lab "$t/pass" 250 | grep -q 'D < -T: no' && echo ok)"
out=$(v --d-only lab "$t/bad" 76); rc=$?
ok "--d-only on a failed log exits 2" "$([ $rc = 2 ] && ! echo "$out" | grep -q 'D <' && echo ok)"
{ echo "salt 2: M A 1 B 1"; cat "$t/d3"; } > "$t/d3salt"
out=$(v lab "$t/pass" "$t/d3salt" "$t/d4"); rc=$?
ok "logs over different salts exit 2" "$([ $rc = 2 ] && ! echo "$out" | grep -qE 'PASS|FAIL$' && echo ok)"
[ $fail = 0 ] && echo "q2_verdict_check: ok"
exit $fail
