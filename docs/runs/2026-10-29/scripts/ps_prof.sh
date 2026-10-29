#!/bin/bash
# ps_prof.sh <exe> <env file>: docs/runs/2026-10-28/scripts/pin_prof.sh with <env file> as the profiled copy's .env
# (the elevated task runs the exe with its own environment, so settings go through <exe>.env).
cp "$2" "$RUN_DIR/bv_prof.exe.env" || exit 6
exec bash "/c/Users/Winston Li/Documents/GitHub/tatic/docs/runs/2026-10-28/scripts/pin_prof.sh" "$1"
