#!/bin/bash
# join_residue.sh <exe>: what do the add3 size-11 held-out laws that stay free-less at JOIN_VISIT 20000 lack: budget, the
# join's size cap, other families' rules, or rules no library has? The exe is HEAD plus patches/join_cap.patch (env
# JOIN_CAP, default 2: the join's cap over the larger side). The add3 salt-1 ref library (run 2026-10-22-gen-warm-fix,
# mon_1) serves the size-band's held_size_11 (run 2026-10-22-size-band) at 20000; the laws still needing a machine proof
# are the residue, served again per arm. Hand rules: and-idempotence and four bitwise-arithmetic bridges. Last, the full
# size-9 and size-11 sets at 2000 with and without both hand sets. Prints per serve as join_budget.sh does.
EXE=$1; T="${RUN_DIR:-$TEMP}/join_residue"; R="$LOCALAPPDATA/claude-runs/tatic/2026-10-22"
mkdir -p "$T"
serve() { # rules laws visit cap tag
  local t0=$(date +%s%N)
  JOIN_VISIT=$3 JOIN_CAP=$4 RULEMINER_FAMILY=add3 CHECK_FAMILY=add3 RULEMINER_DEEP3=1 MACHINE_BANNER=0 \
    CHECK_RULES="$(cygpath -w "$1")" CHECK_LAWFILE="$(cygpath -w "$2")" \
    "$EXE" search::rule_set_kernel_check --exact --ignored --nocapture < /dev/null > "$T/$5.log" 2>&1
  local ms=$(( ($(date +%s%N) - t0) / 1000000 ))
  awk -v tag=$5 -v ms=$ms -v n=$(wc -l < "$2") '/^CHECKED/{f=$5; sub(/\(/,"",f); x=$11} /^JOINED/{j=$2; s=$8; r=$11} END{printf "%s: laws %s free %s not-proved %s joined %s searches %s reached %s ms %s\n", tag, n, f, x, j, s, r, ms}' "$T/$5.log"
}
LIB="$R-gen-warm-fix/mon_1/lib_add3/rules.txt"; S="$R-size-band/size_band/add3"
cat "$R"-gen-warm-fix/mon_1/lib_{add3,sbo3,mix3,cmp3d}/rules.txt > "$T/pooled.txt"
printf '%s\n' 'and(x, and(y, x)) -> and(x, y)' 'and(x, and(x, y)) -> and(x, y)' 'and(x, x) -> x' > "$T/idem.txt"
printf '%s\n' 'sub(or(x, y), xor(x, y)) -> and(x, y)' 'sub(or(x, y), and(x, y)) -> xor(x, y)' \
  'add(xor(x, y), and(x, y)) -> or(x, y)' 'add(or(x, y), and(x, y)) -> add(x, y)' > "$T/bridge.txt"
cat "$LIB" "$T/idem.txt" > "$T/lib_idem.txt"; cat "$LIB" "$T/bridge.txt" > "$T/lib_bridge.txt"
cat "$LIB" "$T/idem.txt" "$T/bridge.txt" > "$T/lib_both.txt"
serve "$LIB" "$S/held_size_11.txt" 20000 2 s11-v20000
sed -n 's/^MACHINE [0-9]* //p' "$T/s11-v20000.log" > "$T/residue.txt"
U="$T/residue.txt"
serve "$LIB" "$U" 20000 2 res-base
serve "$LIB" "$U" 131072 2 res-v131072
for c in 3 4 5; do serve "$LIB" "$U" 131072 $c res-v131072-cap$c; done
serve "$T/pooled.txt" "$U" 20000 2 res-pooled
serve "$T/pooled.txt" "$U" 131072 4 res-pooled-v131072-cap4
for h in idem bridge both; do serve "$T/lib_$h.txt" "$U" 20000 2 res-$h; done
for z in 9 11; do
  serve "$LIB" "$S/held_size_$z.txt" 2000 2 s$z-v2000
  serve "$T/lib_both.txt" "$S/held_size_$z.txt" 2000 2 s$z-v2000-both
done
echo "residue $(wc -l < "$U") laws; still needing a machine proof with both hand sets:"
sed -n 's/^MACHINE [0-9]* /  /p' "$T/res-both.log"
