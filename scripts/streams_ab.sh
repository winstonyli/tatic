#!/bin/bash
# streams_ab.sh <exe A> <exe B> <salts...>: the gate on the streams (spec §9). Per salt, SWEEP=cold:streams (extras
# on, 2 lanes, 6 scoring workers) with A and B, `JOBS` arms at a time (default 1; `ARM_CACHE` reuses arms), each a `runs run` (job
# CPU and wall) into $RUN_DIR/s<salt>_<A|B>; a watchdog stops an arm past 8 GB of private commit (its own process tree, `tree_mem.ps1`). Then per loop the held-out M under the
# loop's final rules (tests/church_bv/held_{11,13}.txt, CHECK_FAST: the laws that still need a whole-term machine
# proof). Per salt, as soon as both its arms are done: M, held-out M and job CPU of each arm, and whether each loop's rules agree; per arm the totals, the
# lookup memo's peak (CLASS_MEMO) and the largest peakproc; per salt and per arm the work counts (the summed WORK lines,
# spec docs/superpowers/specs/2026-10-23-work-counts-design.md). Last line: loops with the same rules, and arms that
# failed (non-zero exit, no M, no WORK line, or a switch of its .exe.env that never took effect); exits 1 if any arm failed. Differing rules are reported, not failed.
a=$1; b=$2; shift 2
root="$(cd "$(dirname "$0")/.." && pwd)"
runs="$root/tools/runs/target/release/runs.exe"
[ -x "$runs" ] || { echo "streams_ab: $runs not built (cargo build --release in tools/runs)"; exit 1; }
# the environments the gate sets, one NAME=value per line: the sweep's (<salt> <out dir>) and the held-out check's
# (<rules file> <law file>, Windows paths); `changed` skips their names
sweep_env() { printf '%s\n' MACHINE_STATE=0 SWEEP=cold:streams "SALT=$1" "SWEEP_OUT=$2"; }
held_env() { printf '%s\n' MACHINE_STATE=0 CHECK_FAST=1 CHECK_FAMILY=streams "CHECK_RULES=$1" "CHECK_LAWFILE=$2"; }
held() { # <exe> <rules file> <arm dir>: held-out M over both bands; the check's ABLATED and ENV lines go to <arm dir>/held_lines.txt
  local m=0 band out line p f n e
  for band in 11 13; do
    mapfile -t e < <(held_env "$(cygpath -w "$2")" "$(cygpath -w "$root/tests/church_bv/held_$band.txt")")
    out=$(env "${e[@]}" "$1" search::rule_set_kernel_check --exact --ignored --nocapture < /dev/null 2>&1)
    grep -E '^(ABLATED|ENV) ' <<< "$out" >> "$3/held_lines.txt"; line=$(grep '^CHECKED ' <<< "$out")
    p=$(echo "$line" | sed -E 's/^CHECKED ([0-9]+) .*/\1/'); f=$(echo "$line" | sed -E 's/.*\(([0-9]+) with.*/\1/'); n=$(echo "$line" | sed -E 's/.*\), ([0-9]+) not proved.*/\1/')
    [ -n "$line" ] || { echo "held: no CHECKED line for $2 band $band" >&2; echo x; return; }
    m=$((m + p - f + n))
  done
  echo $m
}
work() { # <dirs...>: their WORK lines summed per counter, `interp=<n> walk=<n> match=<n> op=<n>`; empty if none
  grep -rh '^WORK ' "$@" 2>/dev/null | awk '{for (i = 2; i <= NF; i++) {split($i, kv, "="); if (!(kv[1] in t)) o[++n] = kv[1]; t[kv[1]] += kv[2]}} END {for (i = 1; i <= n; i++) printf "%s%s=%.0f", (i > 1 ? " " : ""), o[i], t[o[i]]}'
}
# an arm's M and job CPU: <arm dir>
m() { cut -f4 "$1/cold_streams.tsv" 2>/dev/null | grep -E '^[0-9]+$' | awk '{s += $1} END {print s + 0}'; }
c() { grep -oE 'jobcpu=[0-9.]+' "$1/result.txt" | cut -d= -f2; }
# <salt>: its lines once both arms are done (an arm writes `failed` last; the second arm to finish prints, and the
# `mkdir` makes that one arm): the loops whose rules differ, then M, held-out M, job CPU and work of each arm, or which
# arm failed. Printed as each salt finishes, so a reader of the log (the ablations driver) can act before the gate ends.
salt_line() {
  local s=$1 d="$RUN_DIR/s$1" l f fa fb
  fa=$(cat "${d}_A/failed" 2>/dev/null); fb=$(cat "${d}_B/failed" 2>/dev/null)
  [ -n "$fa" ] && [ -n "$fb" ] && mkdir "$RUN_DIR/.s$s.line" 2>/dev/null || return 0
  for l in 1 2 3; do f="cold_streams_streams_${l}_none/rules.txt"; cmp -s "${d}_A/$f" "${d}_B/$f" || echo "salt $s loop $l: rules differ"; done
  [ "$fa$fb" = 00 ] || { echo "salt $s: failed (A $fa B $fb)"; return 0; }
  echo "salt $s: M A $(m "${d}_A") B $(m "${d}_B"); held A $(cat "${d}_A/held.txt") B $(cat "${d}_B/held.txt"); jobcpu A $(c "${d}_A") B $(c "${d}_B"); work A $(work "${d}_A") B $(work "${d}_B")"
}
# <exe>.env <arm dir>: the switches its ABLATE names that never took effect in the arm (no `ABLATED <name>` line, job.rs
# `Setup::ablated`): a misspelled, deleted or unreached switch would make B an unablated copy of A
untaken() {
  local v
  for v in $(sed -nE 's/^ *ABLATE *= *//p' "$1" 2>/dev/null | tr -d ' \r' | tr ',' ' '); do grep -rqsx "ABLATED $v" "$2" || echo "$v"; done
}
# <exe>.env <cache entry>: the first name the cached arm read from its environment (its ENV lines, job.rs `Setup::var`)
# whose value now differs, as `<name>=<then>, now <now>` or `<name> unset, now <now>`; empty when all agree. A value is
# the process's, else its .exe.env's (trimmed, names upper-cased, the first line for a name), as job.rs's merge_env reads
# them; a name bash cannot hold counts as changed. The names the gate sets itself (`sweep_env`, `held_env`) are skipped
changed() {
  local l n was now set
  set=" $({ sweep_env x x; held_env x x; } | sed 's/=.*//' | paste -sd' ') "
  while IFS= read -r l; do
    l=${l#ENV }
    if [[ $l =~ ^([^=\ ]+)=(.*)$ ]]; then n=${BASH_REMATCH[1]}; was="=${BASH_REMATCH[2]}"; else n=${l% unset}; was=" unset"; fi
    [[ $set = *" $n "* ]] && continue
    if ! [[ $n =~ ^[A-Za-z_][A-Za-z0-9_]*$ ]]; then now="=?"
    elif [ -n "${!n+x}" ]; then now="=${!n}"
    else
      now=$(cat "$1" 2>/dev/null | tr -d '\r' | awk -v n="$n" 'index($0, "=") {k = $0; sub(/=.*/, "", k); gsub(/^[ \t]+|[ \t]+$/, "", k)
        if (toupper(k) == n) {sub(/^[^=]*=/, ""); gsub(/^[ \t]+|[ \t]+$/, ""); print "=" $0; exit}}')
      now=${now:- unset}
    fi
    [ "$now" = "$was" ] || { echo "$n$was, now ${now#[= ]}"; return; }
  done < <(grep -rh '^ENV ' "$2" 2>/dev/null | tr -d '\r' | sort -u)
}
# <arm dir> <cache entry>: store a finished arm through a temporary copy, so a reader never sees half an arm. The copy
# is named by the storing arm's own pid ($$ is the script's, shared by the arms of one key in an A/A), and moved with
# `mv -T`, so an entry another writer stored first is kept, not nested into.
cache_put() {
  local t="$2.$BASHPID"
  mkdir -p "${2%/*}"; rm -rf "$t"
  cp -r "$1" "$t" && echo "$1" > "$t/from" && rm -rf "$2" && mv -T "$t" "$2" 2>/dev/null || rm -rf "$t"
}
# <salts...>: the last line, loops whose rules agree and arms that failed; status 1 if any did. An arm failed unless its
# `failed` holds 0: an empty one (an arm stopped mid-write) once ended the count early, and the line read none failed
tally() {
  local s x l f n=0 same=0 loops=0
  for s; do
    for x in A B; do [ "$(cat "$RUN_DIR/s${s}_$x/failed" 2>/dev/null)" = 0 ] || n=$((n + 1)); done
    for l in 1 2 3; do
      f="cold_streams_streams_${l}_none/rules.txt"
      cmp -s "$RUN_DIR/s${s}_A/$f" "$RUN_DIR/s${s}_B/$f" && same=$((same + 1))
      loops=$((loops + 1))
    done
  done
  echo "streams_ab: rules same in $same of $loops loops; $n of $(($# * 2)) arms failed"
  [ $n = 0 ]
}
arm() { # <salt> <A|B>: one arm into $RUN_DIR/s<salt>_<arm>, its sweep then its held-out M; $o/failed holds 1 if it failed
  local s=$1 arm=$2 exe o mb h l v= f=0 c= long e
  [ $arm = A ] && exe=$a || exe=$b
  o="$RUN_DIR/s${s}_$arm"
  # ARM_CACHE=<dir>: an arm that ran without failing is kept under the hash of its exe, the exe's .exe.env, this
  # script, runs.exe and the held-out laws, and an arm with the same hash and salt is copied, not run, if the environment
  # it read is unchanged (`changed`): the gate's results repeat (counts to a few ppm, docs/tier-cycle.md, "Work counts
  # as the gate's cost"). Off by default: an A/A of one exe would otherwise run once.
  # The exe by its long name (here and in the ABLATED check below): the .exe.env of a short (8.3) name like
  # B_COLL~1.EXE does not exist, so B hashed as A (the exe itself reads `<its canonical path>.env`).
  long=$(cygpath -u "$(cygpath -w -l "$exe")")
  if [ -n "${ARM_CACHE:-}" ]; then
    c="$(cygpath "$ARM_CACHE")/$(cat "$long" "$long.env" "$0" "$runs" "$root"/tests/church_bv/held_{11,13}.txt 2>/dev/null | sha256sum | cut -c1-16)/s$s"
    [ "$(cat "$c/failed" 2>/dev/null)" = 0 ] && v=$(changed "$long.env" "$c") && [ -n "$v" ] && echo "salt $s $arm: cached arm read $v"
    if [ "$(cat "$c/failed" 2>/dev/null)" = 0 ] && [ -z "$v" ]; then
      # through a temporary copy, so the other arm never sees this one's `failed` before the rest of it
      rm -rf "$o" "$o.$BASHPID"; cp -r "$c" "$o.$BASHPID" && mv -T "$o.$BASHPID" "$o"; echo "salt $s $arm: reused from $(cat "$o/from")"; salt_line $s; return
    fi
  fi
  mkdir -p "$o"; rm -f "$o/exit" "$o/failed" "$o/held_lines.txt"
  mapfile -t e < <(sweep_env $s "$(cygpath -w "$o")")
  ( "$runs" run "$(cygpath -w "$o")" -- "${e[@]}" "$exe" driver::sweep --exact --ignored --nocapture < /dev/null > "$o/result.txt" 2>&1; echo $? > "$o/exit" ) &
  while [ ! -f "$o/exit" ]; do
    mb=$(powershell -NoProfile -File "$(cygpath -w "$root/scripts/tree_mem.ps1")" -Match "$(cygpath -w "$o")" < /dev/null | tr -d '\r')
    [ "${mb:-0}" -gt 8192 ] && { echo "salt $s $arm: over 8 GB ($mb MB), stopped"; powershell -NoProfile -File "$(cygpath -w "$root/scripts/tree_mem.ps1")" -Match "$(cygpath -w "$o")" -Kill < /dev/null > /dev/null; }
    ping -n 6 127.0.0.1 > /dev/null
  done
  echo "salt $s $arm: exit $(cat "$o/exit") $(tail -1 "$o/result.txt")"
  [ "$(cat "$o/exit")" = 0 ] && cut -f4 "$o/cold_streams.tsv" 2>/dev/null | grep -qE '^[0-9]+$' || f=1
  h=0
  for l in 1 2 3; do v=$(held "$exe" "$o/cold_streams_streams_${l}_none/rules.txt" "$o"); [ "$v" = x ] && f=1 || h=$((h + v)); done
  echo $h > "$o/held.txt"
  grep -rqs '^WORK ' "$o" || f=1
  for v in $(untaken "$long.env" "$o"); do echo "salt $s $arm: ABLATE=$v never took effect"; f=1; done
  echo $f > "$o/failed"
  [ -n "$c" ] && [ $f = 0 ] && cache_put "$o" "$c"
  salt_line $s
}
# JOBS arms at a time (default 1: an arm's job CPU is then clean enough to compare, timed runs keep it); in the order A
# first on odd salts, B first on even ones
for s in "$@"; do
  [ $((s % 2)) = 1 ] && order="A B" || order="B A"
  for x in $order; do
    while [ "$(jobs -rp | wc -l)" -ge "${JOBS:-1}" ]; do wait -n; done
    arm $s $x &
  done
done
wait
for arm in A B; do
  m=0; h=0
  for s in "$@"; do
    for v in $(cut -f4 "$RUN_DIR/s${s}_$arm/cold_streams.tsv" 2>/dev/null | grep -E '^[0-9]+$'); do m=$((m + v)); done
    v=$(cat "$RUN_DIR/s${s}_$arm/held.txt" 2>/dev/null); h=$((h + ${v:-0}))
  done
  memo=$(grep -rh '^CLASS_MEMO' "$RUN_DIR"/s*_$arm 2>/dev/null | awk '{if ($2 > x) x = $2} END {print x + 0}')
  peak=$(grep -h -oE 'peakproc=[0-9]+' "$RUN_DIR"/s*_$arm/result.txt 2>/dev/null | cut -d= -f2 | sort -n | tail -1)
  echo "total $arm: M $m; held $h; $(cat "$RUN_DIR"/s*_$arm/result.txt | grep -oE '(wall|jobcpu)=[0-9.]+' | awk -F= '{t[$1]+=$2} END {printf "wall %.0f s, job cpu %.0f s", t["wall"], t["jobcpu"]}'); memo peak $memo terms; peakproc max $peak; work $(work "$RUN_DIR"/s*_$arm)"
done
tally "$@"
