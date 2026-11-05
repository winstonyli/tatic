#!/usr/bin/env bash
# size_check.sh [root]: no tracked .rs file is over LIMIT lines unless scripts/check/size_allowlist.txt lists it (`path max_lines`).
# The list only shrinks: a listed file over its max fails, and so does one that is now at or under LIMIT or under its max
# (lower the max or delete the line, in the commit that shrank it). Exit 1 listing the offenders.
cd "${1:-$(dirname "$0")/../..}" || exit 2
LIMIT=1000
list=scripts/check/size_allowlist.txt
bad=0
declare -A max
while read -r p m; do [ -n "$p" ] && max[$p]=$m; done < <(grep -v "^#" "$list" | sed 's/\r$//')
declare -A seen
while read -r n p; do
  [ "$p" = total ] && continue
  seen[$p]=1
  m=${max[$p]:-}
  if [ -z "$m" ]; then
    [ "$n" -gt "$LIMIT" ] && { echo "over $LIMIT and not listed: $p ($n lines); split it or, if it must stay, list it"; bad=1; }
  elif [ "$n" -gt "$m" ]; then echo "grew past its max: $p ($n > $m)"; bad=1
  elif [ "$n" -le "$LIMIT" ]; then echo "listed but now within $LIMIT: $p ($n); delete its line"; bad=1
  elif [ "$n" -lt "$m" ]; then echo "shrank: $p ($n < $m); lower its max to $n"; bad=1
  fi
done < <(git ls-files '*.rs' | xargs wc -l)
for p in "${!max[@]}"; do [ -n "${seen[$p]:-}" ] || { echo "listed but not tracked: $p"; bad=1; }; done
[ $bad -eq 0 ] && echo "size_check: ok (${#max[@]} listed)"
exit $bad
