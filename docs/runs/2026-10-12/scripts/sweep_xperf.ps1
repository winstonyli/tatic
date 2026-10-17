# sweep_xperf.ps1 <exe>: records a kernel trace (sampled profile with stacks, context switches, all page faults, virtual
# allocations) over one salt-1 sweep run by `runs run` (children on normal pages, as driver::sweep sets; machine-state
# checks off, so the trace holds only the sweep), to find where the sweep's kernel time goes (docs/tier-cycle.md, "How
# often the large-page stall hits a sweep"). The trace needs admin: it goes through the elevated Samply task's xperf mode
# (~/.claude/samply/profile.ps1 -Mode xperf, set up once by the user), so this script itself runs unelevated. Needs
# tools/runs built (`cargo build --release --manifest-path tools/runs/Cargo.toml`). Writes <run dir>\sweep_xperf\trace.etl
# and the sweep's output to sweep.txt; analysing the trace with `xperf -i` needs no elevation. About a minute, plus the
# merge.
param([Parameter(Mandatory)][string]$exe)
$ErrorActionPreference = 'Stop'
$runs = (Resolve-Path (Join-Path $PSScriptRoot '..\..\..\..\tools\runs\target\release\runs.exe')).Path
$exe = (Resolve-Path $exe).Path
$o = "$(& $runs dir)\sweep_xperf"
Remove-Item -Recurse -Force "$o\sweep" -EA 0
New-Item -ItemType Directory -Force $o | Out-Null
$runArgs = @('run', "$o\sweep", '--', 'MACHINE_STATE=0', 'SALT=1', 'SWEEP=mines own cold pooled', 'MIMALLOC_ALLOW_LARGE_OS_PAGES=0', "SWEEP_OUT=$o\sweep\out", $exe, 'driver::sweep', '--exact', '--ignored', '--nocapture')
& "$env:USERPROFILE\.claude\samply\profile.ps1" -Mode xperf -Exe $runs -Out "$o\trace.etl" -ExeArgs $runArgs | Tee-Object "$o\sweep.txt"
"trace: $o\trace.etl"
