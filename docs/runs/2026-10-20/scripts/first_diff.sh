# first_diff.sh <salts_ab.sh run dir>: per salt and cold loop, the first rule (in the order chosen, cmp3d mine 0) where
# arm A's and arm B's choices differ, and how many A chose.
d=$1
for s in 1 2 3 4 5; do for l in 1 2 3; do
  for a in A B; do grep -h "RULEMINER chosen" "$d/s${s}_$a/cold_cmp3d_cmp3d_${l}_none/mine_0.log" | sed 's/.*: //' > "$TEMP/first_diff_$a.txt"; done
  n=$(cmp "$TEMP/first_diff_A.txt" "$TEMP/first_diff_B.txt" 2>/dev/null | sed -E 's/.*line ([0-9]+).*/\1/')
  echo "s$s l$l first differing rule ${n:-none} of $(wc -l < "$TEMP/first_diff_A.txt")"
done; done
