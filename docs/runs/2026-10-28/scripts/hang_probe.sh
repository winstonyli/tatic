#!/bin/bash
# hang_probe.sh <exe> <salt> [NAME=value...]: reruns one cold:streams sweep that hung in the mines' join-budget probe
# (gates mjv-j0 and mjv-j100n688, salt 3: one mine thread spinning for 1.5-2 h) on a debug-info build of the same code,
# waits for a thread to pass 120 s of CPU (deadline 20 min), samples its stack 40 times (stack_sample.ps1), names the
# frames (stack_names.sh) and stops the sweep. Into $RUN_DIR: the exe copy and its .env, the sweep, samples.txt,
# names.txt, headline.txt.
# the exe by its long name, so its PDB's name follows from it (an 8.3 name like CHURCH~1.EXE does not)
exe=$(cygpath -u "$(cygpath -w -l "$1")"); salt=$2; shift 2; o="$RUN_DIR"; d=$(cygpath -w "$o"); here=$(dirname "$0")
cp "$exe" "$o/bv_hang.exe"; cp "${exe%.exe}.pdb" "$o/$(basename "${exe%.exe}.pdb")"
{ printf 'MACHINE_STATE=0\nSWEEP=cold:streams\nSALT=%s\nSWEEP_OUT=%s\n' "$salt" "$d\\sweep"; printf '%s\n' "$@"; } > "$o/bv_hang.exe.env"
"$o/bv_hang.exe" driver::sweep --exact --ignored --nocapture < /dev/null > "$o/sweep.log" 2>&1 &
# the busiest thread of any bv_hang process once one passes 120 s: "<pid> <tid> <seconds>"
hot() { powershell -NoProfile -Command "Get-Process -Name bv_hang -EA 0 | % { \$p = \$_; \$_.Threads | ? { \$_.TotalProcessorTime.TotalSeconds -gt 120 } | % { '{0} {1} {2:N0}' -f \$p.Id, \$_.Id, \$_.TotalProcessorTime.TotalSeconds } } | select -First 1" < /dev/null | tr -d '\r'; }
dl=$(( $(date +%s) + 1200 )); h=
until h=$(hot); [ -n "$h" ] || [ $(date +%s) -gt $dl ] || ! kill -0 $! 2>/dev/null; do sleep 10; done
if [ -n "$h" ]; then
  set -- $h
  powershell -NoProfile -File "$(cygpath -w "$here/stack_sample.ps1")" -ProcId $1 -ThreadId $2 -Samples 40 -Out "$d\\samples.txt" < /dev/null
  bash "$here/stack_names.sh" "$o/samples.txt" "$o/bv_hang.exe" > "$o/names.txt" 2>&1
  echo "salt $salt: thread $2 of pid $1 at $3 s CPU sampled 40 times; $(grep -m1 -A1 '== rip' "$o/names.txt" | tail -1 | sed 's/^ *//')" > "$o/headline.txt"
else
  echo "salt $salt: no thread passed 120 s of CPU (sweep $(kill -0 $! 2>/dev/null && echo still running || echo ended))" > "$o/headline.txt"
fi
powershell -NoProfile -Command "Get-Process -Name bv_hang -EA 0 | Stop-Process -Force" < /dev/null
wait
cat "$o/headline.txt"
