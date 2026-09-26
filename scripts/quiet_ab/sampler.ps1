# Every 2 s: unix time, _Total CPU % of the machine, and how many
# selfplay*/League* processes exist. Each line covers the 2 s before its
# timestamp. Per-process counters can't attribute load here: processes
# that start and exit between samples (our short runs, other sessions'
# shell commands) never appear in them, about 14% of the machine when
# measured. So own load comes from each run's exact CPU time (pin.ps1),
# and clean.py subtracts it from the total.
# Exits when $parent (ab.sh) is gone, so it never outlives its runner.
param($out, $parent)
while (Get-Process -Id $parent -EA 0) {
  $t = (Get-Counter '\Processor(_Total)\% Processor Time' -SampleInterval 2 -MaxSamples 1).CounterSamples[0].CookedValue
  $sp = @(Get-Process | ? { $_.ProcessName -like 'selfplay*' -or $_.ProcessName -like 'League*' }).Count
  "{0} {1:N1} {2}" -f [DateTimeOffset]::UtcNow.ToUnixTimeSeconds(), $t, $sp | Out-File -Append -Encoding ascii $out
}
