# gate_sum.sh <salts_ab.sh run dir>: per salt and arm, from cold_cmp3d.tsv the summed M, rules, exhausted and joined over
# the three loops, from every serve log's CHECKED line the laws not proved and those that used up the rule budget, and
# from the mines' `RULEMINER join` lines the searches and seconds searching; then the totals per arm. The quality gate
# passes if B's M is not worse and its joined/exhausted are no worse.
d=$1
for o in "$d"/s*_[AB]; do
  arm=${o##*_}; s=$(basename "$o" | sed 's/_.*//')
  t=$(awk -F'\t' '{m+=$4; r+=$6; e+=$8; j+=$9} END {printf "%d %d %d %d", m, r, e, j}' "$o/cold_cmp3d.tsv")
  c=$(grep -h CHECKED "$o"/*/serve_*.log | sed -E 's/.*, ([0-9]+) not proved, ([0-9]+) used up.*/\1 \2/' | awk '{n+=$1; b+=$2} END {printf "%d %d", n, b}')
  j=$(grep -h "RULEMINER join:" "$o"/*/mine_*.log | sed -E 's/.*join: ([0-9]+) searches.*, ([0-9.]+)s searching.*/\1 \2/' | awk '{n+=$1; t+=$2} END {printf "%d %.0f", n, t}')
  echo "$s $arm $t $c $j"
done | sort | awk 'BEGIN {print "salt arm M rules exhausted joined notproved budget searches search_s"} {print; for (i = 3; i <= 10; i++) T[$2, i] += $i}
  END {for (a = 0; a < 2; a++) {x = a ? "B" : "A"; printf "total %s", x; for (i = 3; i <= 10; i++) printf " %d", T[x, i]; print ""}}'
