# Page faults per repeat check (m1's deterministic A/B): for A.exe and B.exe in $env:EXEDIR and d in 11, 13, runs
# measure_cachegrind with GATE_REPS=1 and GATE_REPS=3 (3 runs each) and prints the process's page-fault count
# (GetProcessMemoryInfo on the exited process) and (reps 3 - reps 1) / 2. Load-independent; launch through run.ps1.
Add-Type -Namespace K -Name P -MemberDefinition @'
[StructLayout(LayoutKind.Sequential)] public struct PMC { public uint cb; public uint PageFaultCount; public UIntPtr a,b,c,d,e,f,g,h; }
[DllImport("psapi.dll")] public static extern bool GetProcessMemoryInfo(IntPtr h, out PMC c, uint cb);
'@
function Faults($arm, $d, $reps) {
  $env:GATE_D = $d; $env:GATE_CHECK = '1'; $env:GATE_REPS = $reps
  $p = Start-Process -FilePath (Join-Path $env:EXEDIR "$arm.exe") -ArgumentList '--ignored','--exact','proof::tests::gate::measure_cachegrind','--test-threads','1' -PassThru -WindowStyle Hidden -RedirectStandardOutput "$env:RUN_DIR\o.txt" -RedirectStandardError "$env:RUN_DIR\e.txt"
  $h = $p.Handle; $p.WaitForExit()
  $c = New-Object K.P+PMC; $c.cb = [Runtime.InteropServices.Marshal]::SizeOf($c)
  if (-not [K.P]::GetProcessMemoryInfo($h, [ref]$c, $c.cb) -or $p.ExitCode -ne 0) { throw "run failed: $arm d=$d exit $($p.ExitCode)" }
  $c.PageFaultCount
}
$head = ''
foreach ($d in 11, 13) { foreach ($arm in 'A', 'B') {
  $one = 1..3 | % { Faults $arm $d 1 }; $three = 1..3 | % { Faults $arm $d 3 }
  $per = [int]((($three | sort)[1] - ($one | sort)[1]) / 2)
  "d=$d $arm reps1 $($one -join ',') reps3 $($three -join ',') per-repeat $per"
  $head += "d=$d $arm $per faults per repeat check; "
} }
$head | Out-File -Encoding ascii "$env:RUN_DIR\headline.txt"
