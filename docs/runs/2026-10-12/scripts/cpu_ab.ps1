# cpu_ab.ps1 <exe> <env var> <pairs>: proof_cost_split (cmp3d, own library, 300 laws), the process's CPU seconds with the
# env var unset (old) and set to 1 (new), alternating, pinned to 12 cores at BelowNormal
param([string]$exe, [string]$var, [int]$pairs = 6)
$s = Split-Path -Parent $MyInvocation.MyCommand.Path
$env:CHECK_FAMILY = 'cmp3d'; $env:CHECK_RULES = "$s\cmp3d_own_rules.txt"; $env:RULEMINER_LAWS = '300'
$out = "$env:TEMP\kk\cpu_ab_out.txt"
foreach ($i in 1..$pairs) {
    foreach ($tag in $(if ($i % 2) { 'old', 'new' } else { 'new', 'old' })) {
        if ($tag -eq 'new') { Set-Item "env:$var" '1' } else { Remove-Item "env:$var" -EA 0 }
        $p = Start-Process -FilePath $exe -ArgumentList 'search::proof_cost_split', '--exact', '--ignored', '--nocapture' -PassThru -NoNewWindow -RedirectStandardOutput $out -RedirectStandardError "$out.err"
        $p.PriorityClass = 'BelowNormal'; $p.ProcessorAffinity = 0xFFF
        $p.WaitForExit()
        $cost = (Select-String -Path $out -Pattern 'COST rule-proofs' | Select-Object -First 1).Line -replace '.*(build=\S+ check=\S+).*', '$1'
        "{0} {1} cpu={2:0.00}s {3}" -f $i, $tag, $p.TotalProcessorTime.TotalSeconds, $cost
    }
}
Remove-Item "env:$var" -EA 0
