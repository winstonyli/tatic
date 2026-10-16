# cpu_ab.ps1 <exe> <env var> <pairs> [<new exe>] [<value>]: proof_cost_split (cmp3d, own library, 300 laws), the process's CPU
# seconds with the env var unset (old) and set to <value>, default 1 (new), alternating, pinned to 12 cores at BelowNormal. With <new exe>, old runs
# <exe> and new runs <new exe>, and the env var is never set (pass '-').
param([string]$exe, [string]$var, [int]$pairs = 6, [string]$newexe = '', [string]$val = '1')
$s = Split-Path -Parent $MyInvocation.MyCommand.Path
$env:CHECK_FAMILY = 'cmp3d'; $env:CHECK_RULES = "$s\cmp3d_own_rules.txt"; $env:RULEMINER_LAWS = '300'
$out = "$(& "$PSScriptRoot\kk.ps1")\cpu_ab_out.txt"
foreach ($i in 1..$pairs) {
    foreach ($tag in $(if ($i % 2) { 'old', 'new' } else { 'new', 'old' })) {
        $x = $exe
        if ($newexe) { if ($tag -eq 'new') { $x = $newexe } }
        elseif ($tag -eq 'new') { Set-Item "env:$var" $val } else { Remove-Item "env:$var" -EA 0 }
        $p = Start-Process -FilePath $x -ArgumentList 'search::proof_cost_split', '--exact', '--ignored', '--nocapture' -PassThru -NoNewWindow -RedirectStandardOutput $out -RedirectStandardError "$out.err"
        # Holding the handle keeps the exited process's CPU time readable; without it TotalProcessorTime can come back empty.
        $null = $p.Handle
        $p.PriorityClass = 'BelowNormal'; $p.ProcessorAffinity = 0xFFF
        $p.WaitForExit()
        if ($null -eq $p.TotalProcessorTime) { throw "$i $tag`: CPU time unreadable" }
        $cost = (Select-String -Path $out -Pattern 'COST rule-proofs' | Select-Object -First 1).Line -replace '.*(build=\S+ check=\S+).*', '$1'
        "{0} {1} cpu={2:0.00}s {3}" -f $i, $tag, $p.TotalProcessorTime.TotalSeconds, $cost
    }
}
if (-not $newexe) { Remove-Item "env:$var" -EA 0 }
