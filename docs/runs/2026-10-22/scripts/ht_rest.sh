# ht_rest.sh <exe> <mines run dir> <salt>...: the loop stages `2026-10-22-hidden-twins` skipped (SWEEP=own:add3,sbo3
# cold:add3,sbo3, on the generator-on libraries of <mines run dir>/mon_<s>), into kk.sh's directory as on_on_<s>.
# The skip assumed add3's and sbo3's filtered lists were unchanged by the wider twin key; they were not (spec step 5).
# Prints one line per salt: per stage total M; a non-zero exit or a missing tsv prints FAILED. Last line: sweeps failed.
exe=$1; lib=$2; shift 2
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
runs="$(dirname "$0")/../../../../tools/runs/target/release/runs.exe"
failed=0
for s in "$@"; do
  o="$d/on_on_$s"; mkdir -p "$o"
  "$runs" run "$(cygpath -w "$o")" -- MACHINE_STATE=0 SALT=$s "SWEEP=own:add3,sbo3 cold:add3,sbo3" "SWEEP_OUT=$(cygpath -w "$o")" "LIB=$(cygpath -w "$lib/mon_$s")" "$exe" driver::sweep --exact --ignored --nocapture < /dev/null > "$o/result.txt" 2>&1
  e=$?; line=""
  for st in own cold; do
    f="$o/${st}_add3,sbo3.tsv"; [ -s "$f" ] || { e=missing; continue; }
    line="$line $st $(awk -F'\t' '{t+=$4} END {printf "M %d;", t}' "$f")"
  done
  [ "$e" = 0 ] || { failed=$((failed + 1)); line="FAILED ($e)$line"; }
  echo "salt $s:$line $(grep -oE 'wall=[0-9.]+' "$o/result.txt")"
done
echo "ht_rest: $failed sweeps failed"
[ $failed = 0 ]
