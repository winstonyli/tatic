# Run an exe below normal priority, pinned to 12 cores (FFF: a quarter of
# this 16-core laptop stays free), wait for it,
# print "cpu=<seconds>" (the CPU time of it and every process it starts, exact
# whatever its length; a job object collects the children, which join it
# automatically) as a last line, and exit with its exit code. Affinity and
# priority set just after start apply to every thread the process has by
# then, and to the processes it starts later.
param([Parameter(ValueFromRemainingArguments)] $cmd)
$ErrorActionPreference = 'Stop'
$exe, $rest = $cmd
# Process.Start doesn't find a relative path such as target/ab/bin/x.exe,
# so resolve one that exists here; a bare name still searches PATH.
if (Test-Path -LiteralPath $exe -PathType Leaf) { $exe = (Resolve-Path -LiteralPath $exe).ProviderPath }
$si = New-Object System.Diagnostics.ProcessStartInfo $exe
$si.UseShellExecute = $false
$si.Arguments = ($rest | % { if ($_ -match '[\s"]') { '"' + ($_ -replace '"', '\"') + '"' } else { $_ } }) -join ' '
Add-Type -Namespace QuietAb -Name Job -MemberDefinition @'
[DllImport("kernel32.dll")] public static extern IntPtr CreateJobObject(IntPtr attrs, string name);
[DllImport("kernel32.dll")] public static extern bool AssignProcessToJobObject(IntPtr job, IntPtr process);
[DllImport("kernel32.dll")] public static extern bool QueryInformationJobObject(IntPtr job, int cls, long[] info, int len, IntPtr ret);
'@
$job = [QuietAb.Job]::CreateJobObject([IntPtr]::Zero, $null)
$p = [System.Diagnostics.Process]::Start($si)
# A process that already exited can't be pinned, and needn't be.
try { $p.PriorityClass = 'BelowNormal'; $p.ProcessorAffinity = [IntPtr]0xFFF } catch { if (-not $p.HasExited) { throw } }
$injob = [QuietAb.Job]::AssignProcessToJobObject($job, $p.Handle)
$p.WaitForExit()
[Console]::Out.Flush()
# JOBOBJECT_BASIC_ACCOUNTING_INFORMATION (class 1) starts with total user and
# kernel time, in 100 ns, of every process the job has held
$acct = New-Object long[] 6
if ($injob -and [QuietAb.Job]::QueryInformationJobObject($job, 1, $acct, 48, [IntPtr]::Zero)) { $cpu = ($acct[0] + $acct[1]) / 1e7 }
else { "pin: no job accounting; cpu= counts the launched process only"; $cpu = $p.TotalProcessorTime.TotalSeconds }
"cpu={0:F3}" -f $cpu
exit $p.ExitCode
