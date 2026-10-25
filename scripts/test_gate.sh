#!/bin/bash
# scripts/test_gate.sh: checks of scripts/streams_ab.sh (the gate) and scripts/ablations.sh (its driver), in a sandbox
# under $TEMP; nothing real runs. The gate's arms come from a made-up arm cache, or fail on a fake exe; the driver's
# gates are a fake streams_ab.sh behind a fake run.ps1. Run from the repo root: PASS or FAIL per case, exit 1 on any
# FAIL. About 15-25 min with other jobs running (2026-10-25; main before the bands took 10).
set -u
[ -f scripts/streams_ab.sh ] || { echo "test_gate: run from the repo root"; exit 2; }
repo=$(pwd); T=$(mktemp -d "$TEMP/test_gate.XXXXXX"); fails=0
ok() { # <case> <got> <want>
  if [ "$2" = "$3" ]; then echo "PASS $1"; else echo "FAIL $1"; echo "  got:  $2"; echo "  want: $3"; fails=$((fails + 1)); fi
}

# --- the gate: a root with its scripts and a fake runs.exe (any arm that runs fails), two exes and a cache of arms
mkdir -p "$T/root/scripts" "$T/root/tools/runs/target/release" "$T/root/tests/church_bv"
cp scripts/streams_ab.sh scripts/tree_mem.ps1 "$T/root/scripts/"; echo fake > "$T/root/tools/runs/target/release/runs.exe"
for b in 11 13 15 17; do echo $b > "$T/root/tests/church_bv/held_$b.txt"; done
echo fake > "$T/A.exe"; echo fake > "$T/B.exe"; echo ABLATE=x > "$T/B.exe.env"
# the key streams_ab.sh gives an exe: its bytes, its .exe.env, the script, runs.exe and the held-out laws (in band
# order, as streams_ab.sh's `bands` lists them)
hfiles() { local b; for b in $(ls "$T/root/tests/church_bv" | sed -nE 's/^held_([0-9]+)\.txt$/\1/p' | sort -n); do echo "$T/root/tests/church_bv/held_$b.txt"; done; }
key() { { cat "$1" "$1.env" "$T/root/scripts/streams_ab.sh" "$T/root/tools/runs/target/release/runs.exe"; hfiles | while read -r f; do cat "$f"; done; } 2>/dev/null | sha256sum | cut -c1-16; }
mkarm() { # <dir> <M> <held> <jobcpu> <from>: a finished arm
  local l; mkdir -p "$1"
  for l in 1 2 3; do mkdir -p "$1/cold_streams_streams_${l}_none"; echo "rule $l" > "$1/cold_streams_streams_${l}_none/rules.txt"; done
  printf 'x\tx\tx\t%s\n' "$2" > "$1/cold_streams.tsv"; echo "$3" > "$1/held.txt"; printf '%s\n' "1 11 1000 900 100" "none 11 1000 800 200" > "$1/held_bands.txt"; echo "wall=1s jobcpu=$4" > "$1/result.txt"
  echo "WORK interp=7 walk=1 match=1 op=1" > "$1/out.txt"; echo 0 > "$1/failed"; echo "$5" > "$1/from"
}
mkarm "$T/cache/$(key "$T/A.exe")/s1" 100 500 10 "arm A"; mkarm "$T/cache/$(key "$T/B.exe")/s1" 100 500 11 "arm B"
# what B's cached arm read (job.rs `Setup::var`'s ENV lines, one with CRLF): a name from the environment, an unset one,
# one the gate sets itself
printf 'ENV GATE_T_X=1\r\nENV GATE_T_U unset\nENV SALT=7\n' > "$T/cache/$(key "$T/B.exe")/s1/task.log"; export GATE_T_X=1
gate() { # <run> <B as passed> <salts...>: the gate's output, with the environment the caller sets
  mkdir -p "$T/$1"
  (cd "$T/root" && RUN_DIR=$(cygpath -w "$T/$1") bash scripts/streams_ab.sh "$(cygpath -w "$T/A.exe")" "$2" "${@:3}" < /dev/null 2>/dev/null)
}
B=$(cygpath -w "$T/B.exe"); w="interp=7 walk=1 match=1 op=1"
out=$(ARM_CACHE=$(cygpath -w "$T/cache") gate hit "$B" 1)
ok "cache hit: the salt line" "$(echo "$out" | grep '^salt 1:')" "salt 1: M A 100 B 100; held A 500 B 500; jobcpu A 10 B 11; work A $w B $w"
ok "cache hit: both arms reused" "$(echo "$out" | grep -c 'reused from arm')" 2
ok "cache hit: the last line" "$(echo "$out" | tail -1)" "streams_ab: rules same in 3 of 3 loops; 0 of 2 arms failed"
ok "cache hit: the bands line" "$(echo "$out" | grep '^bands A:')" "bands A: 11 free .900 table .800 M 100.0 table 200.0"
# a fake exe that prints a CHECKED line from its CHECK_LAWFILE's band and its rules file (empty: the table alone); bands
# 9, 11, 15 and 17, so a glob's order (11 before 9) would show
printf '#!/bin/bash\nb=$(head -1 "$(cygpath -u "$CHECK_LAWFILE")"); [ -s "$(cygpath -u "$CHECK_RULES")" ] && f=$((b * 10)) || f=$b\necho "CHECKED 990 laws kernel-checked ($f with no whole-term machine proof), 10 not proved, 0 used up the rule budget"\n' > "$T/F.exe"
mv "$T/root/tests/church_bv/held_13.txt" "$T/root/tests/church_bv/held_9.txt"; echo 9 > "$T/root/tests/church_bv/held_9.txt"
# the loops' rules files, which the failed sweep (fake runs.exe) never writes and the arm does not delete
for l in 1 2 3; do mkdir -p "$T/fake/s1_B/cold_streams_streams_${l}_none"; echo "rule $l" > "$T/fake/s1_B/cold_streams_streams_${l}_none/rules.txt"; done
gate fake "$(cygpath -w "$T/F.exe")" 1 > /dev/null
ok "held: a line per rule set and band, bands in numeric order" "$(paste -sd'|' "$T/fake/s1_B/held_bands.txt" 2>/dev/null)" \
  "1 9 1000 90 910|1 11 1000 110 890|1 15 1000 150 850|1 17 1000 170 830|2 9 1000 90 910|2 11 1000 110 890|2 15 1000 150 850|2 17 1000 170 830|3 9 1000 90 910|3 11 1000 110 890|3 15 1000 150 850|3 17 1000 170 830|none 9 1000 9 991|none 11 1000 11 989|none 15 1000 15 985|none 17 1000 17 983"
ok "held: the total is the loops' M" "$(cat "$T/fake/s1_B/held.txt")" $((3 * (910 + 890 + 850 + 830)))
mv "$T/root/tests/church_bv/held_9.txt" "$T/root/tests/church_bv/held_13.txt"; echo 13 > "$T/root/tests/church_bv/held_13.txt"
# an arm with no band lines (cached before the bands) leaves the summary readable
rm "$T/cache/$(key "$T/A.exe")/s1/held_bands.txt"
ok "an arm with no band lines" "$(ARM_CACHE=$(cygpath -w "$T/cache") gate nobands "$B" 1 | grep '^bands A:')" "bands A: no band lines"
mkarm "$T/cache/$(key "$T/A.exe")/s1" 100 500 10 "arm A"
# a failed band check fails the arm: a runs.exe whose sweep succeeds (M, a WORK line), then F.exe (every check prints
# CHECKED: the arm passes) against G.exe (the table alone's check at band 15 prints none)
printf '#!/bin/bash\nd=$(cygpath -u "$2"); printf "x\\tx\\tx\\t5\\n" > "$d/cold_streams.tsv"; echo "WORK interp=1 walk=1 match=1 op=1"; echo "wall=1s jobcpu=1"\n' > "$T/root/tools/runs/target/release/runs.exe"
sed 's/^echo "CHECKED/[ -s "$(cygpath -u "$CHECK_RULES")" ] || [ "$b" != 15 ] \&\& echo "CHECKED/' "$T/F.exe" > "$T/G.exe"
for x in F G; do for l in 1 2 3; do mkdir -p "$T/ok$x/s1_B/cold_streams_streams_${l}_none"; echo "rule $l" > "$T/ok$x/s1_B/cold_streams_streams_${l}_none/rules.txt"; done; gate ok$x "$(cygpath -w "$T/$x.exe")" 1 > "$T/ok$x.out"; done
ok "every band checked: the arm passes" "$(cat "$T/okF/s1_B/failed")" 0
ok "a band with no CHECKED line fails the arm" "$(cat "$T/okG/s1_B/failed")" 1
# the total and bands lines count only the arms that passed: a failed arm's files would count a salt it never finished
ok "a passed arm counts" "$(grep -oE '^total B: M [0-9]+; held [0-9]+' "$T/okF.out")" "total B: M 5; held $((3 * (890 + 870 + 850 + 830)))"
ok "a failed arm counts nowhere" "$(grep -E '^(total|bands) B:' "$T/okG.out" | paste -sd'|')" "total B: no arm passed|bands B: no arm passed"
echo fake > "$T/root/tools/runs/target/release/runs.exe"
# B's arm is reused only where the environment it read is unchanged (the names the gate sets don't count), and only
# under the same runs.exe and held-out laws
hitb() { ARM_CACHE=$(cygpath -w "$T/cache") gate "$1" "$B" 1 | grep '^salt 1 B:' | head -1; }
ok "a changed variable misses" "$(GATE_T_X=2 hitb envx)" "salt 1 B: cached arm read GATE_T_X=1, now 2"
ok "an unset variable now set misses" "$(GATE_T_U=0 hitb envu)" "salt 1 B: cached arm read GATE_T_U unset, now 0"
ok "a variable read now unset misses" "$(unset GATE_T_X; hitb envgone)" "salt 1 B: cached arm read GATE_T_X=1, now unset"
echo 11b > "$T/root/tests/church_bv/held_11.txt"; ok "changed held-out laws miss" "$(hitb envheld | grep -c reused)" 0
echo 11 > "$T/root/tests/church_bv/held_11.txt"; echo fake2 > "$T/root/tools/runs/target/release/runs.exe"
ok "a changed runs.exe misses" "$(hitb envruns | grep -c reused)" 0; echo fake > "$T/root/tools/runs/target/release/runs.exe"
# a name its .exe.env sets is read from there (trimmed, and upper-cased as on Windows), where the process doesn't set it
printf 'ABLATE=x\n gate_t_x = 1 \n' > "$T/B.exe.env"; mkarm "$T/cache/$(key "$T/B.exe")/s1" 100 500 11 "arm B"
printf 'ENV GATE_T_X=1\nENV GATE_T_U unset\n' > "$T/cache/$(key "$T/B.exe")/s1/task.log"
ok "a variable its .exe.env sets counts" "$(unset GATE_T_X; hitb envfile)" "salt 1 B: reused from arm B"
ok "the process's value goes over its .exe.env's" "$(GATE_T_X=3 hitb envover)" "salt 1 B: cached arm read GATE_T_X=1, now 3"
echo ABLATE=x > "$T/B.exe.env"
echo ABLATE=y > "$T/B.exe.env"
ok "a changed .exe.env misses" "$(ARM_CACHE=$(cygpath -w "$T/cache") gate env "$B" 1 | grep '^salt 1:')" "salt 1: failed (A 0 B 1)"
echo ABLATE=x > "$T/B.exe.env"
ok "no ARM_CACHE: both arms run (and fail)" "$(gate unset "$B" 1 | grep '^salt 1:')" "salt 1: failed (A 1 B 1)"
# a long name passed by its 8.3 short name is keyed by its long name, so its .exe.env counts (it once hashed as A)
cp "$T/B.exe" "$T/B_long_name.exe"; cp "$T/B.exe.env" "$T/B_long_name.exe.env"
if short=$(cygpath -d "$T/B_long_name.exe" 2>/dev/null) && [ "$short" != "$(cygpath -w "$T/B_long_name.exe")" ]; then
  ok "a short name is keyed by its long name" "$(ARM_CACHE=$(cygpath -w "$T/cache") gate short "$short" 1 | grep '^salt 1 B:')" "salt 1 B: reused from arm B"
else echo "SKIP a short name is keyed by its long name (no 8.3 names under $TEMP)"; fi
# both arms finishing at once: exactly one salt line (the mkdir guard), every time
n=0; for i in 1 2 3 4 5 6 7 8; do [ "$(JOBS=2 ARM_CACHE=$(cygpath -w "$T/cache") gate together-$i "$B" 1 | grep -c '^salt 1:')" = 1 ] && n=$((n + 1)); done
ok "two arms at once: one salt line" "$n of 8" "8 of 8"
# two arms storing one entry at once: the entry is whole, nothing nested in it, no temporary copy left
source <(sed -n '/^cache_put() {/,/^}/p' scripts/streams_ab.sh)
mkarm "$T/put/o1" 1 1 1 x; mkarm "$T/put/o2" 1 1 1 x; n=0
for i in 1 2 3 4 5 6 7 8 9 10; do
  rm -rf "$T/put/cache"; ( cache_put "$T/put/o1" "$T/put/cache/k/s1" & cache_put "$T/put/o2" "$T/put/cache/k/s1" & wait )
  [ "$(ls "$T/put/cache/k")" = s1 ] && [ -f "$T/put/cache/k/s1/failed" ] && [ ! -e "$T/put/cache/k/s1/o1" ] && [ ! -e "$T/put/cache/k/s1/o2" ] && n=$((n + 1))
done
ok "two stores at once: one whole entry" "$n of 10" "10 of 10"
# the race's worst order, forced: another writer's entry lands between this store's rm and its mv; it is kept, whole
rm -rf "$T/put/cache"; cache_put "$T/put/o1" "$T/put/cache/k/s1"
rm() { [ "$*" = "-rf $T/put/cache/k/s1" ] || command rm "$@"; }
cache_put "$T/put/o2" "$T/put/cache/k/s1"; unset -f rm
ok "a store after another writer's keeps its entry" "$(cat "$T/put/cache/k/s1/from") $(find "$T/put/cache" -name 's1*' | wc -l)" "$T/put/o1 1"
# every name the gate sets, in the sweep's and the held-out check's environments, is skipped by `changed`: the names
# come from the same functions that set them, so a new one can't miss the list
source <(sed -n '/^sweep_env() {/,/^}/p;/^held_env() {/,/^}/p;/^changed() {/,/^}/p' scripts/streams_ab.sh)
mkdir -p "$T/set"; { sweep_env 1 o; held_env r l; } | sed 's/=.*/=other/; s/^/ENV /' > "$T/set/task.log"
ok "the names the gate sets are skipped" "$(wc -l < "$T/set/task.log") [$(changed "$T/none.env" "$T/set")]" "9 []"
# an arm's switches: each named in its .exe.env must have an ABLATED line somewhere in the arm (a task log, the
# held-out check's lines); spaces and CRLF in the .exe.env are read as job.rs's merge_env reads them
source <(sed -n '/^untaken() {/,/^}/p' scripts/streams_ab.sh)
mkdir -p "$T/abl/arm/task"; echo "ABLATED comm" > "$T/abl/arm/task/1.log"; echo "ABLATED eq_pos" > "$T/abl/arm/held_lines.txt"
printf ' ABLATE = comm,eq_pos\r\n' > "$T/abl/x.env"; ok "every switch took effect" "$(untaken "$T/abl/x.env" "$T/abl/arm")" ""
echo "ABLATE=comm,eq_pos,typo,eq" > "$T/abl/x.env"; ok "a switch with no ABLATED line" "$(untaken "$T/abl/x.env" "$T/abl/arm" | paste -sd' ')" "typo eq"
ok "no .exe.env: nothing to check" "$(untaken "$T/abl/none.env" "$T/abl/arm")" ""
# the last line: an arm whose `failed` is anything but 0 failed, an empty one (an arm stopped mid-write) included; an
# empty one once ended the count early, so the line read "0 of 4 arms failed" and the gate exited 0
source <(sed -n '/^passed() {/p; /^tally() {/,/^}/p' scripts/streams_ab.sh)
for a in s1_A s1_B s2_A s2_B; do mkarm "$T/tally/$a" 1 1 1 x; done; : > "$T/tally/s1_A/failed"
out=$(RUN_DIR=$T/tally tally 1 2); ok "an empty failed file is a failed arm" "$out, exit $?" "streams_ab: rules same in 6 of 6 loops; 1 of 4 arms failed, exit 1"
echo 0 > "$T/tally/s1_A/failed"; out=$(RUN_DIR=$T/tally tally 1 2); ok "no arm failed" "$out, exit $?" "streams_ab: rules same in 6 of 6 loops; 0 of 4 arms failed, exit 0"

# --- the driver: a fake run.ps1 runs its command with scripts/streams_ab.sh swapped for a fake gate, which prints the
# salt lines of a VARIANT
mkdir -p "$T/home/.claude/runs" "$T/fake"
cat > "$T/home/.claude/runs/run.ps1" <<'EOF'
param($Kind, $Name, $Command)
$base = "$env:LOCALAPPDATA\claude-runs\tatic\2026-01-01-$Name"; $d = $base; $i = 2
while (Test-Path $d) { $d = "$base-$i"; $i++ }
New-Item -ItemType Directory -Force $d | Out-Null
$env:RUN_DIR = $d
$cmd = $Command.Replace('scripts/streams_ab.sh', "$env:FIXTURE\streams_ab.sh")
cmd /c "$cmd > `"$d\out.log`" 2>&1"
exit $LASTEXITCODE
EOF
cat > "$T/fake/streams_ab.sh" <<'EOF'
#!/bin/bash
# the fake gate: salt lines by VARIANT; rise, held and stopfail print theirs, then hang until stopped; the others print
# all at once
shift 2
hang() { ping -n 299 127.0.0.1 > /dev/null; l 9 100 500; } # a gate not stopped adds salt 9 to the verdict
w() { echo "work A interp=$1 walk=100 match=50 op=$3 B interp=$2 walk=$4 match=50 op=$5"; }
l() { echo "salt $1: M A 100 B $2; held A 500 B $3; jobcpu A 10 B 11; work A interp=10 walk=10 match=10 op=10 B interp=10 walk=10 match=10 op=10"; }
case $VARIANT in
  rise) l 1 100 500; l 2 101 500; hang ;;
  held) l 1 100 501; hang ;;
  stopfail) echo "salt 1: failed (A 0 B 1)"; l 2 101 500; hang ;;
  check) for s in "$@"; do echo "salt $s: M A 176 B 176; held A 900 B 900; jobcpu A 1 B 1; work A op=1 B op=1"; done
         echo "streams_ab: rules same in 6 of 6 loops; 0 of 4 arms failed" ;;
  *) lines=$(for s in "$@"; do
       [ $VARIANT = missing ] && [ $s = 4 ] && continue
       mb=176; ib=1000; wb=100; oa=10; held="held A 900 B 900"; work="; $(w 1000 $ib 10 100 10)"
       case $VARIANT in
         costs) [ $s = 1 ] && ib=1300 ;;
         mixed) [ $s = 1 ] && ib=1300; wb=80 ;;
         pays) [ $s = 3 ] && mb=177 ;;
         zero) oa=0 ;;
         badline) [ $s = 5 ] && held="held A 900 B ?" ;;
       esac
       work="; $(w 1000 $ib $oa $wb $oa)"
       [ $VARIANT = nowork ] && work=""
       [ $VARIANT = badwork ] && [ $s = 7 ] && work="; work A interp=1000 walk=100 match=50 op=10 B interp=1000 walk=100 match=50"
       echo "salt $s: M A 176 B $mb; $held; jobcpu A 430.0 B 431.0$work"
     done) # one write, so the driver reads none of them or all
     n=0; [ $VARIANT = failed ] && n=1
     printf '%s\nstreams_ab: rules same in 30 of 30 loops; %s of 20 arms failed\n' "$lines" $n; [ $n = 0 ] ;;
esac
EOF
driver() { # <variant> <mode args...>: the driver's VERDICT and DRIVER lines, joined by " | "
  local out="$T/drv-$1"; rm -rf "$out" "$T/lad"; mkdir -p "$out" "$T/lad"
  (cd "$repo" && VARIANT=$1 POLL_S=1 USERPROFILE=$(cygpath -w "$T/home") LOCALAPPDATA=$(cygpath -w "$T/lad") FIXTURE=$(cygpath -w "$T/fake") \
    RUN_DIR=$(cygpath -w "$out") bash scripts/ablations.sh "$T/A.exe" "${@:2}" < /dev/null 2>&1) | grep -E '^(VERDICT|DRIVER)' | paste -sd'|' | sed 's/|/ | /g'
}
free="M A 1760 B 1760; held A 9000 B 9000; jobcpu A 4300 B 4310 (+0.2%); work interp +0.00% walk +0.00% match +0.00% op +0.00%, salts 1,2,3,4,5,6,7,8,9,10"
ok "driver: free" "$(driver free ablate x)" "VERDICT x free: $free"
ok "driver: zero counts are free" "$(driver zero ablate x)" "VERDICT x free: $free"
ok "driver: costs goes on" "$(driver costs ablate x)" "VERDICT x costs: M A 1760 B 1760; held A 9000 B 9000; jobcpu A 4300 B 4310 (+0.2%); work interp +3.00% walk +0.00% match +0.00% op +0.00%, salts 1,2,3,4,5,6,7,8,9,10 | DRIVER done: no switch left"
ok "driver: mixed" "$(driver mixed ablate x)" "VERDICT x mixed: M A 1760 B 1760; held A 9000 B 9000; jobcpu A 4300 B 4310 (+0.2%); work interp +3.00% walk -20.00% match +0.00% op +0.00%, salts 1,2,3,4,5,6,7,8,9,10"
ok "driver: pays" "$(driver pays ablate x)" "VERDICT x pays (rise on salt 3): M A 1760 B 1761; held A 9000 B 9000; jobcpu A 4300 B 4310 (+0.2%), salts 1,2,3,4,5,6,7,8,9,10 | DRIVER done: no switch left"
for v in nowork badline badwork failed missing; do ok "driver: $v is an error" "$(driver $v ablate x)" "VERDICT x error"; done
ok "driver: check" "$(driver check check "$T/A.exe" x)" "VERDICT x check identical"
ok "driver: stops at an M rise" "$(driver rise ablate x)" "VERDICT x pays (rise on salt 2): M A 200 B 201; held A 1000 B 1000; jobcpu A 20 B 22 (+10.0%), salts 1,2 | DRIVER done: no switch left"
ok "driver: stops at a held-out rise" "$(driver held ablate x)" "VERDICT x pays (rise on salt 1): M A 100 B 100; held A 500 B 501; jobcpu A 10 B 11 (+10.0%), salts 1 | DRIVER done: no switch left"
ok "driver: a failed salt does not count, a later rise does" "$(driver stopfail ablate x)" "VERDICT x pays (rise on salt 2): M A 100 B 101; held A 500 B 500; jobcpu A 10 B 11 (+10.0%), salts 2 | DRIVER done: no switch left"
left=$(powershell -NoProfile -Command "@(Get-CimInstance Win32_Process | ? { \$_.ProcessId -ne \$PID -and (\$_.CommandLine -like '*$(basename "$T")\\fake\\streams_ab.sh*' -or \$_.CommandLine -like '*ping -n 299 *') }).Count" < /dev/null | tr -d '\r')
ok "driver: a stopped gate leaves no process" "$left" 0

rm -rf "$T"
echo "test_gate: $fails failed"
[ $fails = 0 ]
