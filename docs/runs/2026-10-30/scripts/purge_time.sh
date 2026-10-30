# purge_time.sh <exe> <rounds>: `runs time` over three arms of search::stream_sequences_are_pinned at one stream thread on
# CPU 8 (--affinity 100): A the default purge (1 s), B MIMALLOC_PURGE_DELAY=-1 (the env var only, no code change), A2 the
# default again (an A/A). Arms alternate per round; job CPU and wall per run go into $RUN_DIR (summary.txt). Launch it
# through run.ps1 -Timed, which holds the CPU lease and refuses a busy machine.
exe=$1; rounds=$2
here=$(dirname "$0"); d=$(cygpath -w "$RUN_DIR"); t=(search::stream_sequences_are_pinned --exact --ignored)
"$here/../../../../tools/runs/target/release/runs.exe" time "$d" --rounds "$rounds" --max-hours 1 --affinity 100 \
  -- A STREAM_THREADS=1 "$exe" "${t[@]}" -- B STREAM_THREADS=1 MIMALLOC_PURGE_DELAY=-1 "$exe" "${t[@]}" -- A2 STREAM_THREADS=1 "$exe" "${t[@]}" < /dev/null
