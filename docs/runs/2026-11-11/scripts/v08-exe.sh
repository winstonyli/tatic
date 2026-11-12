#!/bin/bash
# v08-exe.sh: run the one .exe in %LOCALAPPDATA%\claude-runs\tatic\<folder> with the remaining args, or count it:
#   v08-exe.sh <folder> <args...>           run it (the path never enters a run.ps1 -Command)
#   v08-exe.sh icount <folder> <exeargs>    12 pinned runs under icount.ps1 (-Cpu 4); exeargs comma-separated, no spaces
set -u
mode=run
if [ "${1:-}" = icount ]; then mode=icount; shift; fi
dir="$LOCALAPPDATA/claude-runs/tatic/${1:-}"
[ -d "$dir" ] || { echo "v08-exe: no folder $dir" >&2; exit 2; }
shift
set -- "$@"
exes=("$dir"/*.exe)
[ "${#exes[@]}" -eq 1 ] && [ -f "${exes[0]}" ] || { echo "v08-exe: $dir must hold exactly one .exe" >&2; exit 2; }
exe="${exes[0]}"
if [ "$mode" = icount ]; then
  winexe=$(cygpath -w "$exe")
  powershell -NoProfile -File "$USERPROFILE/.claude/samply/icount.ps1" -Exe "$winexe" -Runs 12 -Cpu 4 -ExeArgs "$1"
else
  "$exe" "$@"
fi
