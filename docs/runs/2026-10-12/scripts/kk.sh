# kk.sh: prints (and creates) the run directory where the scripts here write: $RUN_DIR when ~/.claude/runs/run.ps1
# launched them, so a recorded run writes into its own folder; else this checkout's $TEMP/tatic-runs/<checkout folder>.
# Each checkout (the main one or a worktree) has its own, so a session clearing its runs cannot reach another's.
if [ -n "$RUN_DIR" ]; then d=$(cygpath -u "$RUN_DIR"); else d=$(cygpath -u "$TEMP")/tatic-runs/$(basename "$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"); fi; mkdir -p "$d"; echo "$d"
