# join_work.sh <sweep out dir>...: per dir, the join's work from the mines' `RULEMINER join` lines: searches, seconds
# searching and microseconds per search. An A/B whose arms mine different rules runs different searches, so read its
# time beside these (docs/tier-cycle.md, "Independent join steps in left-to-right order only").
for o in "$@"; do
  cat "$o"/*/mine_*.log | grep "RULEMINER join:" | sed -E 's/.*join: ([0-9]+) searches.*, ([0-9.]+)s searching.*/\1 \2/' |
    awk -v o="$(basename "$o")" '{n += $1; t += $2} END {printf "%s: %d searches, %.1f s searching, %.1f us each\n", o, n, t, n ? t * 1e6 / n : 0}'
done
