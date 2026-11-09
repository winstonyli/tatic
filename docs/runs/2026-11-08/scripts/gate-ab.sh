# gate-ab.sh: times measure_gate_costs (best of 3 per doubling tree) on two tatic test exes, A B A B, each a -Timed
# run.ps1 run named gate-ab-<arm><round>[-t<try>]. A = e1dfa71 (before constant_n), B = fb0bfe2; both with the best-of-3
# edit. A refused run (exit 3, busy machine) is retried once total CPU reads under 25%, up to 45 min per arm.
# Exes in %LOCALAPPDATA%\claude-runs\tatic\gate-ab-exes. Run from the repo root: bash docs/runs/2026-11-08/scripts/gate-ab.sh
D=$(cygpath -sm "$LOCALAPPDATA/claude-runs/tatic/gate-ab-exes")
for round in 1 2; do
  for arm in a b; do
    deadline=$(( $(date +%s) + 2700 ))
    try=1
    while :; do
      name="gate-ab-$arm$round"; [ $try -gt 1 ] && name="$name-t$try"
      powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind bench -Name "$name" -Timed \
        -Command "$D/$arm.exe measure_gate_costs --ignored --nocapture --test-threads 1"
      rc=$?
      echo "$name exit $rc"
      [ $rc -ne 3 ] && break
      [ $(date +%s) -ge $deadline ] && { echo "$arm$round gave up"; break; }
      try=$((try + 1))
      # wait for total CPU under 25% (each sample takes 4 s), then try again
      until [ "$(powershell -NoProfile -Command "[int]((Get-Counter '\Processor(_Total)\% Processor Time' -SampleInterval 2 -MaxSamples 2).CounterSamples[-1].CookedValue)")" -lt 25 ] \
        || [ $(date +%s) -ge $deadline ]; do :; done
    done
  done
done
