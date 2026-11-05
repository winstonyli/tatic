#!/bin/bash
# layout_check.sh [root]: where tracked files live. Scripts sit in a role directory of scripts/ (check/, gate/, study/), none
# directly in it; a .patch sits in docs/runs/<date>/patches/ (a run's switch) or docs/superpowers/spikes/ (a spec's spike).
cd "${1:-$(dirname "$0")/../..}" || exit 2
bad=$(git ls-files scripts | awk -F/ 'NF == 2')
[ -z "$bad" ] || { echo "layout_check: file directly in scripts/ (put it in check/, gate/ or study/):"; echo "$bad"; exit 1; }
bad=$(git ls-files '*.patch' | grep -vE '^(docs/runs/[^/]+/patches|docs/superpowers/spikes)/[^/]+\.patch$')
[ -z "$bad" ] || { echo "layout_check: .patch outside docs/runs/<date>/patches/ and docs/superpowers/spikes/:"; echo "$bad"; exit 1; }
echo "layout_check: ok"
