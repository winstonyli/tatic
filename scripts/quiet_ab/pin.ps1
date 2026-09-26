# Run an exe below normal priority, pinned to 12 cores (FFF: a quarter of
# this 16-core laptop stays free), wait for it,
# print "cpu=<seconds>" (its own CPU time, exact whatever its length) as a
# last line, and exit with its exit code. Affinity and priority set just
# after start apply to every thread the process has by then.
param([Parameter(ValueFromRemainingArguments)] $cmd)
$exe, $rest = $cmd
$si = New-Object System.Diagnostics.ProcessStartInfo $exe
$si.UseShellExecute = $false
$si.Arguments = ($rest | % { if ($_ -match '[\s"]') { '"' + ($_ -replace '"', '\"') + '"' } else { $_ } }) -join ' '
$p = [System.Diagnostics.Process]::Start($si)
# A process that already exited can't be pinned, and needn't be.
try { $p.PriorityClass = 'BelowNormal'; $p.ProcessorAffinity = [IntPtr]0xFFF } catch { if (-not $p.HasExited) { throw } }
$p.WaitForExit()
[Console]::Out.Flush()
"cpu={0:F3}" -f $p.TotalProcessorTime.TotalSeconds
exit $p.ExitCode
