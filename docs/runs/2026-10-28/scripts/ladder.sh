#!/bin/bash
# ladder.sh <exe> <arm dir>...: the truncation ladder (docs/tier-cycle.md "Count and slicing", the middle-ground survey of
# 2026-10-28): each loop's mined library of a finished gate arm (<arm dir>/s<salt>_B/cold_streams_streams_<phase>_none),
# cut down without mining again, and the held-out M of each cut under <exe> (the gate's `held`, copied from
# scripts/streams_ab.sh so the gate's ARM_CACHE hash is untouched). Cuts, per mine, from its `RULEMINER chosen (+F fixed`
# lines in choice order (the rules of mine_<k>.results; rules.txt is mine 0's then mine 1's):
#   full   every rule (the control: must give the gate's held-out M)
#   m0     mine 0's rules only (what mine 1 adds)
#   drop0  rules fixing at least 1 straggler (drops the size-only ones)
#   drop1  rules fixing at least 2
#   stop1  each mine's rules up to and including its first fixing fewer than 2 (a stop rule)
#   stop3  up to and including the third in a row fixing fewer than 2
# Mine seconds are the `RULEMINER time round` lines, each charged to the next chosen rule; seconds after a mine's last
# rule (the rounds that found nothing) count only in `full` and, for mine 0, `m0`. The seconds of drop0 and drop1 are
# what their kept rules' rounds took, a bound no stop rule reaches. Into $RUN_DIR: ladder.tsv (arm salt phase cut rules
# kept_s total_s held), and headline.txt (per arm and cut: rules, kept share of mine seconds, held-out M).
exe=$1; shift
cuts="full m0 drop0 drop1 stop1 stop3"
root="$(cd "$(dirname "$0")/../../../.." && pwd)"
held_env() { printf '%s\n' MACHINE_STATE=0 CHECK_FAST=1 "CHECK_RULES=$1" "CHECK_LAWFILE=$2"; }
bands() { local b; for b in $(ls "$root/tests/church_bv" | sed -nE 's/^held_([0-9]+)\.txt$/\1/p' | sort -n); do echo "$root/tests/church_bv/held_$b.txt"; done; }
held() { # <exe> <rules file> <dir>: held-out M over every band (scripts/streams_ab.sh `held`, without its band files)
  local m=0 hf band out line p f n e t="$3/held_out"
  rm -rf "$t"; mkdir -p "$t"
  while read -r hf; do
    band=${hf##*held_}; band=${band%.txt}
    mapfile -t e < <(held_env "$(cygpath -w "$2")" "$(cygpath -w "$hf")")
    env "${e[@]}" "$1" search::rule_set_kernel_check --exact --ignored --nocapture < /dev/null > "$t/$band" 2>&1 &
  done < <(bands)
  wait
  while read -r hf; do
    band=${hf##*held_}; band=${band%.txt}; out=$(cat "$t/$band")
    line=$(grep '^CHECKED ' <<< "$out")
    [ -n "$line" ] || { echo "held: no CHECKED line for $2 band $band" >&2; echo x; return; }
    p=$(echo "$line" | sed -E 's/^CHECKED ([0-9]+) .*/\1/'); f=$(echo "$line" | sed -E 's/.*\(([0-9]+) with.*/\1/'); n=$(echo "$line" | sed -E 's/.*\), ([0-9]+) not proved.*/\1/')
    m=$((m + p - f + n))
  done < <(bands)
  rm -rf "$t"; echo $m
}
# <mine log>: one line per chosen rule, `<fixed> <seconds>`, then `tail <seconds>` (the rounds after the last rule)
picks() {
  awk '/^RULEMINER time round/ {s += $NF + 0} /^RULEMINER chosen \(/ {f = $3; sub(/^\(\+/, "", f); print f + 0, s; s = 0} END {print "tail", s + 0}' "$1"
}
# <cut> <mine 0|1> <picks file>: the kept rules' indices (1-based, one per line), then `secs <kept seconds>`
keep() {
  awk -v cut="$1" -v k="$2" '
    $1 == "tail" {tail = $2; next}
    {n++; fx[n] = $1; s[n] = $2}
    END {
      stop = n; run = 0
      for (i = 1; i <= n; i++) if (fx[i] < 2) { run++; if ((cut == "stop1" && run == 1) || (cut == "stop3" && run == 3)) { stop = i; break } } else run = 0
      for (i = 1; i <= n; i++) {
        keep = (cut == "full") || (cut == "m0" && k == 0) || (cut == "drop0" && fx[i] >= 1) || (cut == "drop1" && fx[i] >= 2) || (cut ~ /^stop/ && i <= stop)
        if (keep) { print i; secs += s[i] }
      }
      if (cut == "full" || (cut == "m0" && k == 0)) secs += tail
      print "secs", secs
    }' "$3"
}
tsv="$RUN_DIR/ladder.tsv"; printf 'arm\tsalt\tphase\tcut\trules\tkept_s\ttotal_s\theld\n' > "$tsv"
for arm in "$@"; do
  a=$(basename "$arm")
  for sd in "$arm"/s[0-9]*_B; do
    salt=${sd##*/s}; salt=${salt%_B}
    for ld in "$sd"/cold_streams_streams_*_none; do
      phase=${ld##*streams_streams_}; phase=${phase%_none}
      w="$RUN_DIR/$a/s$salt/$phase"; mkdir -p "$w"
      total=0
      for k in 0 1; do
        picks "$ld/mine_$k.log" > "$w/picks_$k"
        awk -F'\t' '$1 == "chosen"' "$ld/mine_$k.results" | cut -f2- > "$w/rules_$k"
        [ "$(grep -vc '^tail' "$w/picks_$k")" = "$(grep -c . "$w/rules_$k")" ] || { echo "ladder: $ld mine $k: chosen lines and rules differ" >&2; exit 1; }
        total=$(awk -v t="$total" '{s += $2} END {printf "%.1f", t + s}' "$w/picks_$k")
      done
      cmp -s <(cat "$w/rules_0" "$w/rules_1") <(grep . "$ld/rules.txt") || { echo "ladder: $ld: rules.txt is not mine 0's then mine 1's" >&2; exit 1; }
      for cut in $cuts; do
        : > "$w/$cut.txt"; kept=0
        for k in 0 1; do
          keep "$cut" "$k" "$w/picks_$k" > "$w/keep_$k"
          grep -v '^secs' "$w/keep_$k" | awk 'NR == FNR {want[$1]; next} FNR in want' - "$w/rules_$k" >> "$w/$cut.txt"
          kept=$(awk -v t="$kept" '/^secs/ {printf "%.1f", t + $2}' "$w/keep_$k")
        done
        m=$(held "$exe" "$w/$cut.txt" "$w")
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$a" "$salt" "$phase" "$cut" "$(grep -c . "$w/$cut.txt")" "$kept" "$total" "$m" | tee -a "$tsv"
      done
    done
  done
done
awk -F'\t' 'NR > 1 {k = $1 " " $4; if (!(k in r)) o[++n] = k; r[k] += $5; ks[k] += $6; ts[k] += $7; h[k] += $8}
  END {for (i = 1; i <= n; i++) {k = o[i]; printf "%s: rules %d, mine seconds %.0f%%, held-out M %d\n", k, r[k], 100 * ks[k] / ts[k], h[k]}}' "$tsv" > "$RUN_DIR/headline.txt"
cat "$RUN_DIR/headline.txt"
