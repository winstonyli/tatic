#!/usr/bin/env bash
# pin.ps1 from bash: pinned, below normal, exit code kept, cpu= last line.
exec powershell -NoProfile -ExecutionPolicy Bypass -File "$(cygpath -w "$(cd "$(dirname "$0")" && pwd)/pin.ps1")" "$@"
