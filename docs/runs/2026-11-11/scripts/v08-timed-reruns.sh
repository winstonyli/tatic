#!/bin/bash
# v08-timed-reruns.sh: the timed reruns of v0.8's untimed gate measurements (PARKED "Timed reruns"), each with the exe
# its untimed run used: the go/no-go (rel vs refl, T9; call vs refl, T10 Step 4b) as 5 interleaved rounds of
# time_doubling_12, the Call weight fit (T12, v08-weight-fit.sh on v08-fit-exe), and the targets (T14, best of 3 inside
# time_targets). Run under run.ps1 -Timed. Writes per-run files to $RUN_DIR and headline.txt with the medians.
set -u
here="$(dirname "$0")"
out="${RUN_DIR:-.}"
d12() { # <exe folder> <file>: one time_doubling_12 run; prints build+check ms
  bash "$here/v08-exe.sh" "$1" proof::tests::gate::time_doubling_12 --ignored --exact --nocapture > "$2" 2>&1 || { echo "$1 failed" >&2; exit 1; }
  grep '^build_ms ' "$2" | awk '{print $2+$4}'
}
med() { sort -n | awk '{v[NR]=$1} END {printf "%.1f", v[int((NR+1)/2)]}'; }
for i in 1 2 3 4 5; do
  for arm in rel refl call; do d12 "v08-$arm-exe" "$out/d12-$arm-$i.txt" >> "$out/d12-$arm.ms"; done
done
echo "go/no-go doubling12 build+check median ms: rel $(med < "$out/d12-rel.ms") refl $(med < "$out/d12-refl.ms") call $(med < "$out/d12-call.ms")" > "$out/summary.txt"
mkdir -p "$out/fit" && RUN_DIR="$out/fit" bash "$here/v08-weight-fit.sh" > /dev/null || { echo "weight fit failed" >&2; exit 1; }
{ echo "weight fit (k tree build check total; doubling12):"; cat "$out/fit/headline.txt"; } >> "$out/summary.txt"
bash "$here/v08-exe.sh" v08-s3-targets-exe proof::tests::gate::time_targets --ignored --exact --nocapture > "$out/targets.txt" 2>&1 || { echo "targets failed" >&2; exit 1; }
{ echo "targets (name cost build_ms check_ms, best of 3):"; grep -E '^[a-z_0-9]+ [0-9]+ [0-9.]+ [0-9.]+$' "$out/targets.txt"; } >> "$out/summary.txt"
cat "$out/summary.txt"
head -1 "$out/summary.txt" > "$out/headline.txt"
