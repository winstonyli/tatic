# hc_rounds.ps1 <old exe> <new exe>: twelve full salt-1 sweeps (sweep_job.ps1, arm normal), six old/new pairs, old first in
# odd pairs and new first in even ones; each line is appended to <run dir, kk.ps1>\hc_rounds.txt, then "hc_rounds ALL".
param([string]$old, [string]$new)
$log = "$(& "$PSScriptRoot\kk.ps1")\hc_rounds.txt"; if (Test-Path $log) { Remove-Item $log }
$job = Join-Path $PSScriptRoot 'sweep_job.ps1'
$r = 110
foreach ($pair in 1..6) {
    $order = if ($pair % 2) { @(@('old', $old), @('new', $new)) } else { @(@('new', $new), @('old', $old)) }
    foreach ($a in $order) {
        $line = powershell -NoProfile -File $job $a[1] normal $r | Select-Object -Last 1
        "$($a[0]) $line" | Out-File -Append -Encoding ascii $log
        $r++
    }
}
'hc_rounds ALL' | Out-File -Append -Encoding ascii $log
