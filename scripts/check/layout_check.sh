#!/bin/bash
# layout_check.sh [root]: where tracked files live. Scripts sit in a role directory of scripts/ (check/, gate/, study/), none
# directly in it; a .patch sits in docs/runs/<date>/patches/ (a run's switch) or docs/superpowers/spikes/ (a spec's spike);
# only scripts/gate/arm_env.sh sets the sweep's output variable (dated scripts are records, and stay out of this).
cd "${1:-$(dirname "$0")/../..}" || exit 2
bad=$(git ls-files scripts | awk -F/ 'NF == 2')
[ -z "$bad" ] || { echo "layout_check: file directly in scripts/ (put it in check/, gate/ or study/):"; echo "$bad"; exit 1; }
bad=$(git ls-files '*.patch' | grep -vE '^(docs/runs/[^/]+/patches|docs/superpowers/spikes)/[^/]+\.patch$')
[ -z "$bad" ] || { echo "layout_check: .patch outside docs/runs/<date>/patches/ and docs/superpowers/spikes/:"; echo "$bad"; exit 1; }
bad=$(git grep -l 'SWEEP_OUT[=]' -- scripts tools | grep -vx 'scripts/gate/arm_env.sh')
[ -z "$bad" ] || { echo "layout_check: a sweep recipe outside scripts/gate/arm_env.sh (source it):"; echo "$bad"; exit 1; }
echo "layout_check: ok"
