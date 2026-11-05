#!/bin/bash
# script_header_check.sh [root]: every tracked script under docs/runs/*/scripts/ (.sh .py .ps1 .awk) says what it is in its first
# four lines (a `#` comment other than the shebang, or a docstring), so `grep -m1 -E '^(#[^!]|""")' docs/runs/*/scripts/*` lists them.
cd "${1:-$(dirname "$0")/../..}" || exit 2
bad=$(git ls-files 'docs/runs/*/scripts/*.sh' 'docs/runs/*/scripts/*.py' 'docs/runs/*/scripts/*.ps1' 'docs/runs/*/scripts/*.awk' |
  while read -r f; do sed -n 1,4p "$f" | grep -qE '^\s*(#[^!]|""")' || echo "$f"; done)
[ -z "$bad" ] || { echo "script_header_check: no header comment in:"; echo "$bad"; exit 1; }
echo "script_header_check: ok"
