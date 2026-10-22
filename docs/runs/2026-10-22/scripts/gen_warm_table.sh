# gen_warm_table.sh <run dir>...: the tables of gen_warm.sh's runs (plan docs/superpowers/plans/2026-10-22-generator-warm-ref.md,
# Task 3), over every salt the run dirs hold. Arms: mon/moff (ref mines with the generator on/off), and loops <lib>_<gen>
# (lib: which ref mines' libraries they start from; gen: their own extras). Prints:
# - ref mines, mon against moff: per family the summed M and rules, and the extras' share (n over the mine's b x k laws);
# - per stage (own, cross, pooled, mixed, cold) and loop arm: total M and mined-batch M (batches 1-2, counted from 0), summed over salts;
# - paired counts on each stage's total M per salt, first arm against second: salts better / equal / worse.
#   loop extras: off_on vs off_off, on_on vs on_off; ref extras on the loops: on_off vs off_off, on_on vs off_on; both:
#   on_on vs off_off (cold: only on_on and off_off run it).
rows=$(mktemp)
for d in "$@"; do
  for o in "$d"/*_[0-9]*/; do
    o=${o%/}; arm=$(basename "$o"); s=${arm##*_}; arm=${arm%_*}
    case $arm in
      mon|moff)
        for f in "$o"/mines.tsv "$o"/mines_u3.tsv; do
          [ -s "$f" ] && awk -F'\t' -v a=$arm -v s=$s '{print "mine", a, s, $1, $3, $4}' "$f"
        done
        [ $arm = mon ] && grep -h "^GEN .*lib_" "$o/out.txt" | sed -E 's/.*lib_([a-z0-9]+): L ([0-9]+) n ([0-9]+).*/gen \1 \2 \3/' | awk -v s=$s '{print $1, "mon", s, $2, $3, $4}'
        ;;
      *)
        for st in own cross pooled mixed cold; do
          f="$o/$st.tsv"
          [ -s "$f" ] && awk -F'\t' -v a=$arm -v s=$s -v st=$st '{split($5,m,","); t+=$4; mb+=m[2]+m[3]} END {print "loop", a, s, st, t, mb}' "$f"
        done
        ;;
    esac
  done
done > "$rows"
echo "salts: $(awk '{print $3}' "$rows" | sort -un | tr '\n' ' ')"
echo "== ref mines (summed over salts): family, M on / off, rules on / off, extras n per mine / its b x k laws"
awk '
  $1 == "mine" {m[$4, $2] += $5; r[$4, $2] += $6; fam[$4] = 1}
  $1 == "gen" {n[$4] = $6}
  END {
    split("sbo3 50 add3 50 mix3 50 cmp3d 100 u3 100", b)
    for (i = 1; i < 10; i += 2) bk[b[i]] = 4 * b[i + 1]
    for (f in fam) printf "%-6s M %d / %d  rules %d / %d  extras %d / %d\n", f, m[f, "mon"], m[f, "moff"], r[f, "mon"], r[f, "moff"], n[f], bk[f]
  }' "$rows" | sort
echo "== loops (summed over salts): stage, arm, total M, mined-batch M"
awk '$1 == "loop" {t[$4 " " $2] += $5; mb[$4 " " $2] += $6} END {for (k in t) printf "%-7s %-8s M %4d  mined %4d\n", substr(k, 1, index(k, " ") - 1), substr(k, index(k, " ") + 1), t[k], mb[k]}' "$rows" | sort
echo "== paired, total M per salt: better / equal / worse (first arm against second)"
for pair in "off_on off_off loop-extras" "on_on on_off loop-extras" "on_off off_off ref-extras" "on_on off_on ref-extras" "on_on off_off both"; do
  set -- $pair
  for st in own cross pooled mixed cold; do
    awk -v a=$1 -v b=$2 -v st=$st -v what=$3 '
      $1 == "loop" && $4 == st && ($2 == a || $2 == b) {v[$2, $3] = $5; salts[$3] = 1}
      END {
        for (s in salts) if ((a, s) in v && (b, s) in v) { n++; if (v[a, s] < v[b, s]) bt++; else if (v[a, s] == v[b, s]) eq++; else wr++ }
        if (n) printf "%-11s %-7s %s vs %s: %d / %d / %d\n", what, st, a, b, bt, eq, wr
      }' "$rows"
  done
done
rm -f "$rows"
