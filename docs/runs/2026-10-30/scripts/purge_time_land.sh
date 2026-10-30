# purge_time_land.sh <old exe> <new exe> <rounds> [threads=1] [affinity hex=100]: `runs time` as purge_time.sh, with the arms: A the old exe (default purge, 1 s),
# B the new exe (P1 landed: the purge off in Setup::process, no env var), A2 the old exe with MIMALLOC_PURGE_DELAY=-1 (the
# measurement P1 rests on). The summary's labels read: "B - A" is landed against default, "A2 - A" is the env var against default,
# so the landing holds if B - A matches A2 - A. Launch through run.ps1 -Timed.
old=$1; new=$2; rounds=$3; th=${4:-1}; aff=${5:-100}
here=$(dirname "$0"); d=$(cygpath -w "$RUN_DIR"); t=(search::stream_sequences_are_pinned --exact --ignored)
"$here/../../../../tools/runs/target/release/runs.exe" time "$d" --rounds "$rounds" --max-hours 1 --affinity "$aff" \
  -- A STREAM_THREADS=$th "$old" "${t[@]}" -- B STREAM_THREADS=$th "$new" "${t[@]}" -- A2 STREAM_THREADS=$th MIMALLOC_PURGE_DELAY=-1 "$old" "${t[@]}" < /dev/null
