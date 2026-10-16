# cpu_arms.ps1 <exe> <rounds> <arm>...: proof_cost_split (cmp3d, own library, 300 laws) once per arm per round, the arms'
# order rotating each round. An arm is 'name:VAR=value;VAR=value' (or 'name:' for none); its variables are set for its run
# only. Prints CPU seconds, peak working set and peak private bytes per run; pinned to 12 cores at BelowNormal.
param([string]$exe, [int]$rounds = 4, [Parameter(ValueFromRemainingArguments)][string[]]$arms)
$s = Split-Path -Parent $MyInvocation.MyCommand.Path
$env:CHECK_FAMILY = 'cmp3d'; $env:CHECK_RULES = "$s\cmp3d_own_rules.txt"; $env:RULEMINER_LAWS = '300'
$out = "$(& "$PSScriptRoot\kk.ps1")\cpu_arms_out.txt"
# The exited process's peaks, read through the handle `Start-Process` keeps (`Process.PeakWorkingSet64` reads 0 after exit).
Add-Type -Namespace K -Name Mem -MemberDefinition @'
[StructLayout(LayoutKind.Sequential)] public struct PMC { public uint cb; public uint PageFaultCount; public UIntPtr PeakWorkingSetSize, WorkingSetSize, QuotaPeakPagedPoolUsage, QuotaPagedPoolUsage, QuotaPeakNonPagedPoolUsage, QuotaNonPagedPoolUsage, PagefileUsage, PeakPagefileUsage; }
[DllImport("psapi.dll")] public static extern bool GetProcessMemoryInfo(IntPtr h, out PMC c, uint cb);
'@
function peaks($h) { $c = New-Object K.Mem+PMC; $null = [K.Mem]::GetProcessMemoryInfo($h, [ref]$c, [Runtime.InteropServices.Marshal]::SizeOf($c)); ($c.PeakWorkingSetSize.ToUInt64() / 1MB), ($c.PeakPagefileUsage.ToUInt64() / 1MB) }
foreach ($r in 1..$rounds) {
    foreach ($j in 0..($arms.Count - 1)) {
        $name, $vars = $arms[($j + $r) % $arms.Count] -split ':', 2
        $set = @($vars -split ';' | ? { $_ } | % { $k, $v = $_ -split '=', 2; Set-Item "env:$k" $v; $k })
        $p = Start-Process -FilePath $exe -ArgumentList 'search::proof_cost_split', '--exact', '--ignored', '--nocapture' -PassThru -NoNewWindow -RedirectStandardOutput $out -RedirectStandardError "$out.err"
        # Holding the handle keeps the exited process's CPU time readable.
        $null = $p.Handle
        $p.PriorityClass = 'BelowNormal'; $p.ProcessorAffinity = 0xFFF
        $p.WaitForExit()
        $set | % { Remove-Item "env:$_" -EA 0 }
        $cost = (Select-String -Path $out -Pattern 'COST rule-proofs' | Select-Object -First 1).Line -replace '.*(build=\S+ check=\S+).*', '$1'
        $ws, $priv = peaks $p.Handle
        "{0} {1} cpu={2:0.00}s peakws={3:0}MB peakpriv={4:0}MB {5}" -f $r, $name, $p.TotalProcessorTime.TotalSeconds, $ws, $priv, $cost
    }
}
