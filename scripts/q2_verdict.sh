#!/bin/bash
# q2_verdict.sh <label> <ctx gate log> <small draw 3 log> <small draw 4 log>
# q2_verdict.sh --d-only <label> <gate log> <T>
# The pre-registered Q2 rule (docs/superpowers/plans/2026-11-01-ctx-scorer-q2.md, "Reading a result") over `streams_ab.sh` logs.
# The ctx log has A = `small` at draw 0, B = `ctx`; the redraw logs have A = `small` at draws 3 and 4 (B ignored). Each log must end
# `<k> of <a> arms failed` with k = 0 and the same <a> in all three. Prints
#   <label>: small <H0> walk <W0>; ctx <Hc> walk <Wc>; spread <S>; threshold <T>; held diff <D>; work ratio <R>; PASS|FAIL
# with S = max(|H3 - H0|, |H4 - H0|), T = max(76, S), D = Hc - H0, R = Wc / W0; PASS iff D < -T and R <= 1.05.
# --d-only: A and B of one log are small and ctx at one draw; prints `<label>: D <D>; work ratio <R>; D < -T: yes|no`.
# Exit 0 with a line, 2 on a malformed or failed log (no verdict line).
die() { echo "q2_verdict: $*" >&2; exit 2; }
# facts <log>: `<arms> <H_A> <W_A> <H_B> <W_B>` from the log's last line and its last `total A:` / `total B:` lines
facts() {
  [ -f "$1" ] || die "$1: no such log"
  awk '
    /^total A:/ { a = $0 } /^total B:/ { b = $0 } { last = $0 }
    function held(s) { return match(s, /held [0-9]+/) ? substr(s, RSTART + 5, RLENGTH - 5) : "" }
    function walk(s) { return match(s, /walk=[0-9]+/) ? substr(s, RSTART + 5, RLENGTH - 5) : "" }
    END {
      if (!match(last, /[0-9]+ of [0-9]+ arms failed$/)) exit 3
      split(substr(last, RSTART), p, " ")
      if (p[1] != 0) exit 4
      if (held(a) == "" || walk(a) == "" || held(b) == "" || walk(b) == "") exit 5
      print p[3], held(a), walk(a), held(b), walk(b)
    }' "$1" || die "$1: not a clean gate log (last line must end '0 of <a> arms failed'; totals need held and walk)"
}
if [ "$1" = --d-only ]; then
  label=$2 t=$4
  read -r _ h0 w0 hc wc <<< "$(facts "$3")" || exit 2
  awk -v l="$label" -v d="$((hc - h0))" -v w0="$w0" -v wc="$wc" -v t="$t" 'BEGIN { printf "%s: D %d; work ratio %.3f; D < -T: %s\n", l, d, wc / w0, (d < -t) ? "yes" : "no" }'
  exit 0
fi
[ $# = 4 ] || die "usage: q2_verdict.sh <label> <ctx log> <small d3 log> <small d4 log> | --d-only <label> <log> <T>"
label=$1
read -r n0 h0 w0 hc wc <<< "$(facts "$2")" || exit 2
read -r n3 h3 _ _ _ <<< "$(facts "$3")" || exit 2
read -r n4 h4 _ _ _ <<< "$(facts "$4")" || exit 2
[ "$n0" = "$n3" ] && [ "$n0" = "$n4" ] || die "arm counts differ across the logs ($n0, $n3, $n4)"
awk -v l="$label" -v h0="$h0" -v w0="$w0" -v hc="$hc" -v wc="$wc" -v h3="$h3" -v h4="$h4" 'function abs(x) { return x < 0 ? -x : x }
  BEGIN {
    s = abs(h3 - h0); if (abs(h4 - h0) > s) s = abs(h4 - h0)
    t = s > 76 ? s : 76; d = hc - h0; r = wc / w0
    printf "%s: small %d walk %d; ctx %d walk %d; spread %d; threshold %d; held diff %d; work ratio %.3f; %s\n", l, h0, w0, hc, wc, s, t, d, r, (d < -t && r <= 1.05) ? "PASS" : "FAIL"
  }'
