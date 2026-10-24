# tree_mem.ps1 -Match <text> [-Kill]: the private commit (MB, what peakproc counts; a working set can read 7 MB while
# 1.4 GB is committed) of the process trees rooted at the processes whose command
# line contains <text> (roots included), and with -Kill stops those trees (taskkill /T). streams_ab.sh's watchdog, matched
# on an arm's own output directory so another session running the same exe is neither counted nor stopped.
param([Parameter(Mandatory)][string]$Match, [switch]$Kill)
$all = Get-CimInstance Win32_Process
$roots = @($all | ? { $_.CommandLine -and $_.CommandLine.Contains($Match) -and $_.ProcessId -ne $PID })
$tree = @{}; $todo = [System.Collections.Queue]::new(); $roots | % { $todo.Enqueue($_.ProcessId) }
while ($todo.Count) { $p = $todo.Dequeue(); if ($tree.ContainsKey($p)) { continue }; $tree[$p] = 1; $all | ? { $_.ParentProcessId -eq $p } | % { $todo.Enqueue($_.ProcessId) } }
[int](($all | ? { $tree.ContainsKey($_.ProcessId) } | Measure-Object PrivatePageCount -Sum).Sum / 1MB)
if ($Kill) { $roots | % { taskkill /T /F /PID $_.ProcessId | Out-Null } }
