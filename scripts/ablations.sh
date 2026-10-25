#!/bin/bash
# The class-table ablations (docs/superpowers/plans/2026-10-23-class-table-ablations.md). Run from the repo root.
#   scripts/ablations.sh <A exe> ablate <switch>...   per switch: B = A + B.exe.env ABLATE=<switch>; salts 1-10 of
#                                          scripts/streams_ab.sh in one run; pays at an M or held-out rise on any salt, the gate
#                                          stopped at the first; else by the work counts: costs goes on, mixed and free exit
#   scripts/ablations.sh <deleted exe> check <ablated-from exe> <switch>   salts 1-2, deleted against ablated: identical or differs
# Every run is untimed through run.ps1, pinned to CFF at below-normal priority, 4 arms at a time: no verdict reads job
# CPU. Arms are kept in $runs_root/arm-cache (streams_ab.sh's ARM_CACHE): A runs once per build, and a rerun after a
# stopped driver reuses every arm that finished.
# Tests: scripts/test_gate.sh. POLL_S (default 30): seconds between looks at a running gate's log.
set -u
[ -z "${ABLATE:-}" ] || { echo "driver: ABLATE=$ABLATE is set in the environment; it would reach both arms"; exit 2; }
[ -f scripts/streams_ab.sh ] || { echo "driver: run from the repo root"; exit 2; }
runs_root="$(cygpath "$LOCALAPPDATA")/claude-runs/tatic"
wrap="$(cygpath -w "$USERPROFILE/.claude/runs/run.ps1")"
[ -n "${RUN_DIR:-}" ] || { echo "driver: launch through run.ps1 (no RUN_DIR)"; exit 2; }
here=$(cygpath "$RUN_DIR")
# run from a copy in the run's folder: bash reads a script as it runs, so an edit or a checkout during a run would
# change the running driver
[ "$0" -ef "$here/ablations.sh" ] || { cp "$0" "$here/ablations.sh" && exec bash "$here/ablations.sh" "$@"; }
cp "$1" "$here/A.exe" || exit 2
mode=$2; shift 2

gate() { # <name> <A exe> <B exe> <salts...>: the "salt N:" and streams_ab lines in $here/<name>.txt; 0 ok, 1 failed
  # (or a salt asked for has no line), 2 stopped at the first salt whose B rises (M or held-out M), with the lines of the
  # salts finished by then
  local name=$1 a b rc dir pid before rise=
  a=$(cygpath -d "$2"); b=$(cygpath -d "$3"); shift 3
  # run.ps1 names the folder <date>-<name>, adding -2, -3 to a name an earlier driver run already used: ours is the new one
  folders() { ls -d "$runs_root"/*-"$name" "$runs_root"/*-"$name"-[0-9]* 2>/dev/null; }
  before=$(folders)
  ARM_CACHE=$(cygpath -w "$runs_root/arm-cache") JOBS=4 powershell -NoProfile -File "$wrap" -Kind gate -Name "$name" \
    -Command "start /b /wait /belownormal /affinity CFF bash scripts/streams_ab.sh $a $b $*" < /dev/null > /dev/null 2>&1 &
  pid=$!
  while kill -0 $pid 2>/dev/null; do
    ping -n $((${POLL_S:-30} + 1)) 127.0.0.1 > /dev/null
    dir=$(folders | grep -vxF "$before" | head -1)
    [ -n "$dir" ] && rise=$(risen "$dir/out.log") && [ -n "$rise" ] || continue
    # a rise settles the verdict (pays): stop the gate's streams_ab (not run.ps1, which then closes its row); finished arms
    # are already in the arm cache. Its whole tree is listed first and stopped parents first: `taskkill /T` stops children
    # first, and a script whose child was stopped went on to its next command before its own stop (about 1 stop in 4 in test_gate.sh)
    echo "gate $name: B rises on salt $rise, stopping it"
    powershell -NoProfile -Command "\$all = @(Get-CimInstance Win32_Process)
      \$hit = @(\$all | ? { \$_.Name -ne 'powershell.exe' -and \$_.CommandLine -like '*streams_ab.sh*$b*' })
      \$tree = @(\$hit | ? { \$hit.ProcessId -notcontains \$_.ParentProcessId })
      for (\$i = 0; \$i -lt \$tree.Count; \$i++) { \$tree += @(\$all | ? { \$_.ParentProcessId -eq \$tree[\$i].ProcessId -and \$tree.ProcessId -notcontains \$_.ProcessId }) }
      \$tree | % { Stop-Process -Id \$_.ProcessId -Force -ErrorAction SilentlyContinue }" < /dev/null > /dev/null 2>&1
    break
  done
  wait $pid; rc=$?
  dir=$(folders | grep -vxF "$before" | head -1)
  echo "gate $name: exit $rc, $dir"
  grep -E '^salt [0-9]+:|^streams_ab' "$dir/out.log" > "$here/$name.txt" 2>/dev/null
  cat "$here/$name.txt"
  [ -n "$rise" ] && return 2
  [ $rc = 0 ] && grep -qE ' 0 of [0-9]+ arms failed' "$here/$name.txt" && parsed "$here/$name.txt" &&
    [ "$(salts "$here/$name.txt")" = "$(printf '%s\n' "$@" | sort -n | paste -sd,)" ]
}
# <gate log>: the first salt, in the order the gate finished them, whose B has more M or held-out M than its A
# (streams_ab.sh prints a salt's line once both its arms are done; a failed salt's line does not parse)
risen() { cols "$1" | awk '$3 > $2 || $5 > $4 {print $1; exit}'; }
# <gate lines>: the salts whose line parses, sorted, comma-separated: what a verdict read. A gate run to its end must
# have one for every salt it was asked for (a missing line would leave its salt out of the verdict unseen)
salts() { cols "$1" | awk '{print $1}' | sort -n | paste -sd,; }
# per salt line, one row per counter: salt name A B
wcols() { sed -nE 's/^salt ([0-9]+): .*; work A (.*) B (.*)$/\1|\2|\3/p' "$@" | awk -F'|' '{na = split($2, x, " "); split($3, y, " "); for (i = 1; i <= na; i++) {split(x[i], p, "="); split(y[i], q, "="); print $1, p[1], p[2], q[2]}}'; }
# each counter's tolerance: max(its A/A spread, 1%); the spreads are a few ppm (docs/tier-cycle.md, "Work counts as the
# gate's cost")
tols="interp=0.01 walk=0.01 match=0.01 op=0.01"
# columns of "salt N: M A a B b; held A a B b; jobcpu A a B b": salt mA mB hA hB cA cB
cols() { sed -nE 's/^salt ([0-9]+): M A ([0-9]+) B ([0-9]+); held A ([0-9x]+) B ([0-9x]+); jobcpu A ([0-9.]+) B ([0-9.]+).*/\1 \2 \3 \4 \5 \6 \7/p' "$@"; }
# every salt line parses, in cols and in wcols with an A and a B count per counter: a line either drops would leave its
# salt out of the verdict, and a counter missing on one side would read as a change of 100%
parsed() {
  local n; n=$(cat "$@" | grep -c '^salt ')
  [ "$(cols "$@" | wc -l)" = "$n" ] || return 1
  wcols "$@" | awk -v n="$n" 'NF != 4 || $3 !~ /^[0-9]+$/ || $4 !~ /^[0-9]+$/ {bad = 1} {s[$1]} END {for (k in s) m++; exit bad || m != n}'
}

if [ "$mode" = check ]; then
  sw=$2; cp "$1" "$here/B.exe" || exit 2; echo "ABLATE=$sw" > "$here/B.exe.env"
  gate "check-$sw" "$here/A.exe" "$here/B.exe" 1 2; [ $? = 1 ] && { echo "VERDICT $sw check error"; exit 1; }
  same=$(cols "$here/check-$sw.txt" | awk '$2 != $3 || $4 != $5 {d++} END {print d + 0}')
  if [ "$same" = 0 ] && grep -q 'rules same in 6 of 6 loops' "$here/check-$sw.txt"; then echo "VERDICT $sw check identical"
  else echo "VERDICT $sw check differs"; fi
  exit 0
fi

for sw in "$@"; do
  cp "$here/A.exe" "$here/B_$sw.exe"; echo "ABLATE=$sw" > "$here/B_$sw.exe.env"
  f="$here/abl-$sw.txt"
  gate "abl-$sw" "$here/A.exe" "$here/B_$sw.exe" 1 2 3 4 5 6 7 8 9 10; [ $? = 1 ] && { echo "VERDICT $sw error"; exit 1; }
  sum=$(cols "$f" | awk '{mA+=$2; mB+=$3; hA+=$4; hB+=$5; cA+=$6; cB+=$7} END {printf "M A %d B %d; held A %d B %d; jobcpu A %.0f B %.0f (%+.1f%%)", mA, mB, hA, hB, cA, cB, 100*(cB-cA)/cA}')
  rise=$(cols "$f" | awk '$3 > $2 || $5 > $4 {printf "%s salt %s", (n++ ? "," : ""), $1}')
  if [ -n "$rise" ]; then echo "VERDICT $sw pays (rise on$rise): $sum, salts $(salts "$f")"; continue; fi
  # the counters (spec docs/superpowers/specs/2026-10-23-work-counts-design.md, decision 6(d)): each summed over the
  # salts, against its tolerance
  v=$(wcols "$f" | awk -v tols="$tols" 'BEGIN {n = split(tols, t, " "); for (i = 1; i <= n; i++) {split(t[i], kv, "="); tol[kv[1]] = kv[2]}}
      {if (!($2 in a)) o[++k] = $2; a[$2] += $3; b[$2] += $4}
      END {for (i = 1; i <= k; i++) {c = o[i]; d = a[c] ? (b[c] - a[c]) / a[c] : (b[c] ? 1 : 0); s = s sprintf(" %s %+.2f%%", c, 100 * d)
           if (d > tol[c]) up = 1; else if (d < -tol[c]) dn = 1}
           print (up ? (dn ? "mixed" : "costs") : "free") ":" s}')
  echo "VERDICT $sw ${v%%:*}: $sum; work${v#*:}, salts $(salts "$f")"
  case "${v%%:*}" in costs) continue ;; *) exit 0 ;; esac
done
echo "DRIVER done: no switch left"
