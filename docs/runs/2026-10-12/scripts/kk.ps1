# kk.ps1: prints (and creates) this checkout's run directory, $env:TEMP\tatic-runs\<checkout folder>, where the scripts
# here write. Each checkout (the main one or a worktree) has its own, so a session clearing its runs cannot reach another's.
$d = Join-Path $env:TEMP "tatic-runs\$(Split-Path -Leaf (git -C $PSScriptRoot rev-parse --show-toplevel))"
New-Item -ItemType Directory -Force $d | Out-Null; $d
