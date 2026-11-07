# m2: wall, CPU and peak private bytes, large pages on against off by MIMALLOC_ALLOW_LARGE_OS_PAGES, arms alternating.
$m = "$env:LOCALAPPDATA\m2"; $out = "$env:RUN_DIR\time.tsv"
"work`tround`tpos`tarm`twall_s`tcpu_s`tpeak_mb`texit" | Out-File -Encoding utf8 $out
function One($work, $exe, $argl, $r, $pos, $arm) {
  if ($arm -eq 'off') { $env:MIMALLOC_ALLOW_LARGE_OS_PAGES = '0' } else { Remove-Item Env:MIMALLOC_ALLOW_LARGE_OS_PAGES -ErrorAction SilentlyContinue }
  $psi = New-Object Diagnostics.ProcessStartInfo $exe, $argl
  $psi.UseShellExecute = $false; $psi.RedirectStandardOutput = $false; $psi.WorkingDirectory = $m
  $sw = [Diagnostics.Stopwatch]::StartNew(); $p = [Diagnostics.Process]::Start($psi); $h = $p.Handle
  $peak = 0; while (-not $p.WaitForExit(200)) { try { $p.Refresh(); $v = $p.PeakPagedMemorySize64; if ($v -gt $peak) { $peak = $v } } catch {} }
  $sw.Stop(); $p.WaitForExit()
  "$work`t$r`t$pos`t$arm`t$([math]::Round($sw.Elapsed.TotalSeconds,2))`t$([math]::Round($p.TotalProcessorTime.TotalSeconds,2))`t$([math]::Round($peak/1MB))`t$($p.ExitCode)" | Out-File -Append -Encoding utf8 $out
}
foreach ($r in 1..8) { $o = if ($r % 2) { 'on','off' } else { 'off','on' }; $i = 1; foreach ($a in $o) { One 'proof' "$m\cb.exe" 'proof-cost-split' $r $i $a; $i++ } }
foreach ($r in 1..2) { $o = if ($r % 2) { 'on','off' } else { 'off','on' }; $i = 1; foreach ($a in $o) { One 'tests' "$m\tb.exe" '--skip machine::mimalloc_defaults_to_large_pages' $r $i $a; $i++ } }
"m2 times done" | Out-File -Encoding ascii "$env:RUN_DIR\headline.txt"
