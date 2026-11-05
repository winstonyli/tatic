#!/bin/bash
# gate.sh <exe A> <exe B> <salts...>: the untimed gate (docs/tier-cycle/, "Under load too"), JOBS=3 with the arm cache.
export JOBS=3 ARM_CACHE="$LOCALAPPDATA/claude-runs/tatic/arm-cache"
cd "$(dirname "$0")/../.." && exec scripts/gate/streams_ab.sh "$@"
