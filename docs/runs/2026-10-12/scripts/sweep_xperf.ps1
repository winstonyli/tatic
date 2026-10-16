# sweep_xperf.ps1 <exe>: run from an elevated PowerShell. Records a kernel trace (sampled profile with stacks, context
# switches, all page faults, virtual allocations) over one salt-1 sweep run by sweep_job.ps1 (children on normal pages, as
# driver::sweep sets), to find where the sweep's 37-40% kernel time goes (docs/tier-cycle.md, "How often the large-page
# stall hits a sweep"). Writes <run dir, kk.ps1>\sweep_xperf\trace.etl and the sweep's line to sweep.txt; analysing the trace with
# `xperf -i` needs no elevation. About a minute, plus the merge.
param([string]$exe)
$s = Split-Path -Parent $MyInvocation.MyCommand.Path; $o = "$(& "$PSScriptRoot\kk.ps1")\sweep_xperf"
New-Item -ItemType Directory -Force $o | Out-Null
xperf -on PROC_THREAD+LOADER+PROFILE+CSWITCH+DISPATCHER+ALL_FAULTS+VIRT_ALLOC -stackwalk Profile -BufferSize 1024 -MinBuffers 512 -MaxBuffers 1024 -f "$o\kernel.etl"
if ($LASTEXITCODE) { throw "xperf -on failed ($LASTEXITCODE); is this PowerShell elevated?" }
try {
    powershell -NoProfile -File "$s\sweep_job.ps1" $exe normal 90 | Tee-Object "$o\sweep.txt"
} finally {
    xperf -d "$o\trace.etl"
    Remove-Item "$o\kernel.etl" -EA 0
}
"trace: $o\trace.etl"
