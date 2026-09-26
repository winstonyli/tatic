#!/usr/bin/env bash
# Interleaved A/B that waits out other sessions' jobs and discards runs
# they touched (RELATED_WORK.md §66). On this laptop other sessions run
# back-to-back jobs with short gaps, so a quiet check before a run isn't
# enough: sampler.ps1 logs total CPU through the runs, and clean.py keeps
# only runs no one else loaded.
#
#   scripts/quiet_ab/ab.sh DIR PAIRS MAXHOURS -- A-cmd... -- B-cmd...
#   python scripts/quiet_ab/clean.py DIR/samples.log DIR/runs.log
#
# e.g. the fib(16) probe, a test binary against itself:
#   p="scripts/quiet_ab/pin.sh $exe fib16_instance_proof_cost --ignored --nocapture"
#   scripts/quiet_ab/ab.sh target/ab/fib 10 3 -- $p -- $p
# A round runs A then B (odd rounds) or B then A, each after 60 s under
# 20% total CPU with no selfplay*/League* process (another session's
# jobs). Extract each metric from DIR/{A,B}.N.txt for the rounds where
# clean.py says both runs are clean, and compare bests.
# Each command runs with {r} replaced by the round, stdout to DIR/{A,B}.{r}.txt;
# wrap it in pin.sh, whose cpu= line lets clean.py subtract the run's own load.
# Stops at PAIRS clean pairs, MAXHOURS, a failed run, or when DIR/stop
# exists (checked between runs). Logs to DIR/runs.log.
set -u
D=$(mkdir -p "$1" && cd "$1" && pwd) PAIRS=$2 MAXH=$3; shift 4
A=(); while [ "$1" != -- ]; do A+=("$1"); shift; done; shift; B=("$@")
# A reused DIR would mix its old rounds into clean.py's count, and its old
# samples into the first quiet check; a launch that died before writing
# runs.log still leaves samples.log, so refuse on either.
[ -e "$D/runs.log" -o -e "$D/samples.log" ] && { echo "$D/runs.log or $D/samples.log exists; use a fresh DIR" >&2; exit 2; }
# Commands run from the caller's directory, so relative paths work.
W=$PWD S=$(cd "$(dirname "$0")" && pwd); cd "$D"
powershell -NoProfile -Command "(Get-Process -Id $(cat /proc/$$/winpid)).PriorityClass = 'BelowNormal'"
# Started from bash, which quotes arguments for Windows programs;
# PowerShell 5.1's Start-Process splits paths with spaces.
powershell -NoProfile -File "$(cygpath -w "$S/sampler.ps1")" "$(cygpath -w "$D/samples.log")" "$(cat /proc/$$/winpid)" &
cat /proc/$!/winpid > sampler.pid
powershell -NoProfile -Command "(Get-Process -Id $(cat sampler.pid)).PriorityClass = 'BelowNormal'"
trap 'powershell -NoProfile -Command "Stop-Process -Id $(cat sampler.pid) -EA 0"' EXIT
deadline=$(( $(date +%s) + MAXH * 3600 )); r=0; clean=0
quiet() { # the last 30 samples (60 s): no selfplay/League, total under 20%
  tail -30 samples.log 2>/dev/null | awk '{ if ($3 > 0 || $2 >= 20) bad = 1; n++ } END { exit !(n >= 30 && !bad) }'
}
run() { # label round cmd...
  local l=$1 rr=$2; shift 2; local s=$(date +%s)
  (cd "$W" && exec "${@//\{r\}/$rr}") > "$l.$rr.txt" 2>&1; local rc=$?
  local cpu=$(grep -o '^cpu=[0-9.]*' "$l.$rr.txt" | tail -1)
  echo "run $l $rr $s $(date +%s) rc=$rc ${cpu:-cpu=?}" >> runs.log
  # A failing command would only fail again; stop and say where to look.
  if [ $rc -ne 0 ]; then echo "$(date +%T) $l.$rr failed (rc=$rc); see $D/$l.$rr.txt" >> runs.log; exit 1; fi
}
echo "$(date +%T) start pairs=$PAIRS rtp=$(powershell -NoProfile -Command '(Get-MpComputerStatus).RealTimeProtectionEnabled')" >> runs.log
rm -f stop
while [ $clean -lt $PAIRS ] && [ $(date +%s) -lt $deadline ] && [ ! -e stop ]; do
  until quiet || [ $(date +%s) -ge $deadline ] || [ -e stop ]; do sleep 10; done
  [ $(date +%s) -ge $deadline ] || [ -e stop ] && break
  r=$((r + 1))
  if [ $((r % 2)) -eq 1 ]; then run A $r "${A[@]}"; run B $r "${B[@]}"; else run B $r "${B[@]}"; run A $r "${A[@]}"; fi
  clean=$(python "$S/clean.py" samples.log runs.log | awk '{c[$2] += ($3 == "clean")} END { n = 0; for (k in c) if (c[k] == 2) n++; print n }')
  echo "$(date +%T) round $r done, clean pairs $clean" >> runs.log
done
echo "$(date +%T) done rtp=$(powershell -NoProfile -Command '(Get-MpComputerStatus).RealTimeProtectionEnabled')" >> runs.log
