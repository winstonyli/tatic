# gen_warm.sh <exe> <salt>...: the law generator on ref mines and warm loops (law-generator spec step 4; plan
# docs/superpowers/plans/2026-10-22-generator-warm-ref.md). Per salt, into kk.sh's directory ($RUN_DIR under run.ps1):
# mon_<s> and moff_<s>, the ref mines (SWEEP=$MINES_SWEEP) with the generator on and with ABLATE=gen; then the loops
# (SWEEP=$LOOP_SWEEP) as <lib>_<gen>_<s>: lib on/off reads mon_<s>/moff_<s> through LIB=, gen on/off is the loops' own
# extras (off: ABLATE=gen). Cold loops read no library, so only on_on and off_off add $COLD_SWEEP. ARMS picks the loop
# arms (default all four). Each sweep is a `runs run` (wall, job CPU); a watchdog stops the exe past 8 GB. Prints one line
# per sweep: ref mines' M per family, or per stage total M and mined-batch M (batches 1-2, counted from 0); a sweep with a non-zero exit
# or a missing tsv prints FAILED and counts. Last line: sweeps failed; exits 1 if any did.
exe=$1; shift
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
runs="$(dirname "$0")/../../../../tools/runs/target/release/runs.exe"
[ -x "$runs" ] || { echo "gen_warm: $runs not built (cargo build --release in tools/runs)"; exit 1; }
name=$(basename "$exe" | sed 's/\.[Ee][Xx][Ee]$//')
mines=${MINES_SWEEP:-mines mines:u3}
loops=${LOOP_SWEEP:-own cross pooled mixed}
cold=${COLD_SWEEP-cold}
failed=0; total=0
# sweep <dir> <SWEEP> [VAR=value...]: one sweep of salt $s into <dir>
sweep() {
  local o=$1 sw=$2; shift 2
  mkdir -p "$o"; rm -f "$o/exit"
  ( "$runs" run "$(cygpath -w "$o")" -- MACHINE_STATE=0 SALT=$s "SWEEP=$sw" "SWEEP_OUT=$(cygpath -w "$o")" "$@" "$exe" driver::sweep --exact --ignored --nocapture < /dev/null > "$o/result.txt" 2>&1; echo $? > "$o/exit" ) &
  while [ ! -f "$o/exit" ]; do
    mb=$(powershell -NoProfile -Command "[int]((Get-Process $name -EA 0 | Measure-Object WorkingSet64 -Sum).Sum/1MB)" < /dev/null | tr -d '\r')
    [ "${mb:-0}" -gt 8192 ] && { echo "$o: over 8 GB ($mb MB), stopped"; taskkill //F //IM "$name.exe" > /dev/null; }
    ping -n 6 127.0.0.1 > /dev/null
  done
  wait
  total=$((total + 1))
  local line="" ok=1 st f
  for st in $sw; do
    f="$o/${st//:/_}.tsv"
    if [ ! -s "$f" ]; then ok=0; line="$line $st MISSING;"; continue; fi
    if [ "${st%%:*}" = mines ]; then
      line="$line $(awk -F'\t' '$3 !~ /^[0-9]+$/ {bad=1} {printf "%s M %s rules %s secs %s, ", $1, $3, $4, $2} END {if (bad) printf "BAD "}' "$f")"
    else
      line="$line $st $(awk -F'\t' '$4 !~ /^[0-9]+$/ {bad=1} {split($5,m,","); t+=$4; mb+=m[2]+m[3]; r+=$6; c+=$7} END {printf "M %d mined %d rules %d loop secs %d%s;", t, mb, r, c, bad ? " BAD" : ""}' "$f")"
    fi
  done
  case "$line" in *MISSING*|*BAD*) ok=0 ;; esac
  [ "$(cat "$o/exit")" = 0 ] || ok=0
  [ $ok = 1 ] || { failed=$((failed + 1)); line="FAILED (exit $(cat "$o/exit"))$line"; }
  echo "salt $s $(basename "$o"):$line $(grep -oE '(wall|jobcpu)=[0-9.]+' "$o/result.txt" | tr '\n' ' ')"
}
for s in "$@"; do
  sweep "$d/mon_$s" "$mines"
  sweep "$d/moff_$s" "$mines" ABLATE=gen
  for arm in ${ARMS:-on_on off_on on_off off_off}; do
    lib=${arm%_*}; gen=${arm#*_}
    sw=$loops; [ "$arm" = on_on ] || [ "$arm" = off_off ] && sw="$loops $cold"
    vars=("LIB=$(cygpath -w "$d/m${lib}_$s")"); [ "$gen" = off ] && vars+=(ABLATE=gen)
    sweep "$d/${arm}_$s" "$sw" "${vars[@]}"
  done
done
echo "gen_warm: $failed of $total sweeps failed"
[ $failed = 0 ]
