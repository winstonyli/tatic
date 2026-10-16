# kk.sh: prints (and creates) this checkout's run directory, $TEMP/tatic-runs/<checkout folder>, where the scripts here
# write. Each checkout (the main one or a worktree) has its own, so a session clearing its runs cannot reach another's.
d=$(cygpath -u "$TEMP")/tatic-runs/$(basename "$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"); mkdir -p "$d"; echo "$d"
