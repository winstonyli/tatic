#!/bin/bash
# Reports for prof.sh's traces: per-function sample weight (`-a profile -detail`, user names from the copied PDB, kernel
# names from Microsoft's server) and the process list, for each d<N>.etl in RUN, written beside it. Run with RUN set to
# a c1-xperf run folder; the first run fetches symbols into %LOCALAPPDATA%\xperf-sym (SAMPLY.md).
set -e
cd "${RUN:?RUN=<run folder>}"
mkdir -p "$LOCALAPPDATA/xperf-sym"
export _NT_SYMCACHE_PATH="$LOCALAPPDATA\\xperf-sym\\symcache"
export _NT_SYMBOL_PATH="$(cygpath -w "$RUN");srv*$LOCALAPPDATA\\xperf-sym\\sym*https://msdl.microsoft.com/download/symbols"
for f in d*.etl; do
    b=${f%.etl}
    xperf -tle -tti -i "$f" -symbols -o "$b.profile.txt" -a profile -detail | cat
    xperf -tle -tti -i "$f" -o "$b.process.txt" -a process | cat
done
