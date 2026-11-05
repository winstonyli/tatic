#!/usr/bin/env bash
# Checks every `path#symbol` cite in docs/TOUR.md: the path (a file, or a directory searched whole) exists and the symbol appears in it verbatim.
# Exit 1 listing the broken cites. A renamed or deleted symbol fails here; a changed meaning does not (CLAUDE.md rule).
cd "$(dirname "$0")/../.." || exit 2
tour=docs/TOUR.md
[ -f "$tour" ] || { echo "no $tour"; exit 2; }
bad=0
n=0
while IFS= read -r cite; do
  path=${cite%%#*}
  sym=${cite#*#}
  n=$((n + 1))
  if [ ! -e "$path" ]; then
    echo "missing path: $cite"; bad=$((bad + 1))
  elif ! grep -rqF -- "$sym" "$path"; then
    echo "missing symbol: $cite"; bad=$((bad + 1))
  fi
done < <(grep -oE '`[A-Za-z0-9_./-]+#[^`]+`' "$tour" | tr -d '`' | sort -u)
echo "$n cites checked, $bad broken"
[ "$bad" -eq 0 ]
