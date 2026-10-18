# history_check.sh <exe> <salt>: whether a loop's result depends on the loops run before it in its lane, and through what.
# SWEEP=cold:cmp3d (extras on) three ways, into kk.sh's directory: `one` (1 lane: each loop after the ones before it, on
# one worker and one lemma file), `fresh` (3 lanes: each loop on its own worker and lemma file), `recheck` (1 lane with
# LEMMA_RECHECK=1: one worker, but every lemma built as on an empty file). Prints wall seconds and, per loop, which runs'
# rules.txt agree with `fresh`'s.
exe=$1; s=$2
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
for arm in one:1 fresh:3 recheck:1; do
  name=${arm%:*}; lanes=${arm#*:}
  (
    [ $name = recheck ] && export LEMMA_RECHECK=1
    o="$d/$name"; mkdir -p "$o"; t0=$(date +%s)
    MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=$s SWEEP_LANES=$lanes SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1
    echo "$name: exit $? wall $(( $(date +%s) - t0 )) s"
  )
done
for r in "$d"/fresh/*/rules.txt; do
  l=${r#"$d"/fresh/}
  echo "$l: one $(cmp -s "$r" "$d/one/$l" && echo same || echo differs), recheck $(cmp -s "$r" "$d/recheck/$l" && echo same || echo differs)"
done
