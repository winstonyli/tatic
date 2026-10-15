# sweep_job.ps1 <exe> <large|normal> <round>: one full salt-1 sweep inside a job object holding this PowerShell, so every
# child the sweep spawns is counted; 'normal' sets MIMALLOC_ALLOW_LARGE_OS_PAGES=0. Prints the job's CPU, the largest
# single process's peak commit and the job's peak commit (which includes this PowerShell). Run one fresh PowerShell per
# sweep (`powershell -NoProfile -File sweep_job.ps1 ...`), since the job keeps counting until its last process exits.
param([string]$exe, [string]$arm, [int]$r)
Add-Type -Namespace K -Name Job -MemberDefinition @"
[StructLayout(LayoutKind.Sequential)] public struct BASIC { public long TotalUserTime, TotalKernelTime, ThisPeriodTotalUserTime, ThisPeriodTotalKernelTime; public uint TotalPageFaultCount, TotalProcesses, ActiveProcesses, TotalTerminatedProcesses; }
[StructLayout(LayoutKind.Sequential)] public struct LIMIT { public long PerProcessUserTimeLimit, PerJobUserTimeLimit; public uint LimitFlags; public UIntPtr MinimumWorkingSetSize, MaximumWorkingSetSize; public uint ActiveProcessLimit; public UIntPtr Affinity; public uint PriorityClass, SchedulingClass; }
[StructLayout(LayoutKind.Sequential)] public struct IO { public ulong a, b, c, d, e, f; }
[StructLayout(LayoutKind.Sequential)] public struct EXT { public LIMIT Basic; public IO Io; public UIntPtr ProcessMemoryLimit, JobMemoryLimit, PeakProcessMemoryUsed, PeakJobMemoryUsed; }
[DllImport("kernel32.dll")] public static extern IntPtr CreateJobObject(IntPtr a, string n);
[DllImport("kernel32.dll")] public static extern bool AssignProcessToJobObject(IntPtr j, IntPtr p);
[DllImport("kernel32.dll")] public static extern bool QueryInformationJobObject(IntPtr j, int c, out BASIC i, uint n, IntPtr r);
[DllImport("kernel32.dll")] public static extern bool QueryInformationJobObject(IntPtr j, int c, out EXT i, uint n, IntPtr r);
"@
$job = [K.Job]::CreateJobObject([IntPtr]::Zero, $null)
if (-not [K.Job]::AssignProcessToJobObject($job, (Get-Process -Id $PID).Handle)) { throw 'assign failed' }
if ($arm -eq 'normal') { $env:MIMALLOC_ALLOW_LARGE_OS_PAGES = '0' }
$out = "$env:TEMP\kk\lp_sweep_${arm}_$r"; if (Test-Path $out) { Remove-Item -Recurse -Force $out }; New-Item -ItemType Directory $out | Out-Null
$env:SWEEP_OUT = $out; $env:SALT = '1'; $env:SWEEP = 'mines own cold pooled'
$t = Get-Date
$p = Start-Process -FilePath $exe -ArgumentList 'driver::sweep','--exact','--ignored','--nocapture' -PassThru -NoNewWindow -RedirectStandardOutput "$out\log.txt" -RedirectStandardError "$out\err.txt"
$null = $p.Handle; $p.PriorityClass = 'BelowNormal'; $p.ProcessorAffinity = 0xFFF; $p.WaitForExit()
$b = New-Object K.Job+BASIC; $null = [K.Job]::QueryInformationJobObject($job, 1, [ref]$b, [Runtime.InteropServices.Marshal]::SizeOf($b), [IntPtr]::Zero)
$e = New-Object K.Job+EXT; $null = [K.Job]::QueryInformationJobObject($job, 9, [ref]$e, [Runtime.InteropServices.Marshal]::SizeOf($e), [IntPtr]::Zero)
$mb = 1048576
$ms = (Select-String -Path "$out\err.txt" -Pattern 'machine at' | select -First 1).Line
"{0} {1} wall={2:0.0}s jobcpu={3:0.0}s kernel={9:0.00}s procs={4} peakproc={5:0}MB peakjob={6:0}MB exit={7} | {8}" -f $r, $arm, ((Get-Date) - $t).TotalSeconds, (($b.TotalUserTime + $b.TotalKernelTime) / 1e7), $b.TotalProcesses, ($e.PeakProcessMemoryUsed.ToUInt64() / $mb), ($e.PeakJobMemoryUsed.ToUInt64() / $mb), $p.ExitCode, $ms, ($b.TotalKernelTime / 1e7)
