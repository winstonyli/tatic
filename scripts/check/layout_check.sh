#!/bin/bash
# layout_check.sh [root]: every tracked file under scripts/ sits in a role directory (check/, gate/, study/), none directly in scripts/.
cd "${1:-$(dirname "$0")/../..}" || exit 2
bad=$(git ls-files scripts | awk -F/ 'NF == 2')
[ -z "$bad" ] || { echo "layout_check: file directly in scripts/ (put it in check/, gate/ or study/):"; echo "$bad"; exit 1; }
echo "layout_check: ok"
