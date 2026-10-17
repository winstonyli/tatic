# sweep_xperf.ps1 <exe>: run from an elevated PowerShell. Records a kernel trace (sampled profile with stacks, context
# switches, all page faults, virtual allocations) over one salt-1 sweep run by `runs run` (children on normal pages, as
# driver::sweep sets; machine-state checks off, so the trace holds only the sweep), to find where the sweep's kernel time
# goes (docs/tier-cycle.md, "How often the large-page stall hits a sweep"). Needs tools/runs built
# (`cargo build --release --manifest-path tools/runs/Cargo.toml`). Writes <run dir>\sweep_xperf\trace.etl and the sweep's
# line to sweep.txt; analysing the trace with `xperf -i` needs no elevation. About a minute, plus the merge.
param([string]$exe)
$runs = Join-Path $PSScriptRoot '..\..\..\..\tools\runs\target\release\runs.exe'
$o = "$(& $runs dir)\sweep_xperf"
New-Item -ItemType Directory -Force $o | Out-Null
xperf -on PROC_THREAD+LOADER+PROFILE+CSWITCH+DISPATCHER+ALL_FAULTS+VIRT_ALLOC -stackwalk Profile -BufferSize 1024 -MinBuffers 512 -MaxBuffers 1024 -f "$o\kernel.etl"
if ($LASTEXITCODE) { throw "xperf -on failed ($LASTEXITCODE); is this PowerShell elevated?" }
try {
    & $runs run "$o\sweep" -- MACHINE_STATE=0 SALT=1 'SWEEP=mines own cold pooled' MIMALLOC_ALLOW_LARGE_OS_PAGES=0 "SWEEP_OUT=$o\sweep\out" $exe driver::sweep --exact --ignored --nocapture | Tee-Object "$o\sweep.txt"
} finally {
    xperf -d "$o\trace.etl"
    Remove-Item "$o\kernel.etl" -EA 0
}
"trace: $o\trace.etl"
