#!/bin/bash
# held_prune.sh <exe>: a throwaway prototype of a held-out backward pass (PARKED.md, "A held-out backward pass after
# each mine"), frontier side only. Per family, the salt-1 ref library (run 2026-10-22-gen-warm-fix, mon_1) is pruned in
# one pass, last-chosen rule first: a rule is dropped if the pruning set A does not lose free laws (no whole-term
# machine proof) without it. Arm `held` looks at A only; arm `both` also requires the mine's own laws (laws_mine_ref)
# not to lose any. A = run 2026-10-22-size-band's held-out laws of sizes 9 and 11 (salt 11). The scoring set B is
# generated here at salt 21 by `search::size_band_laws` (the exe needs `docs/runs/2026-10-22/patches/size_band_probe.patch`),
# less every line of A and of the mine's laws. Prints per family and arm the rules kept, then free laws under no rules,
# the whole library and each pruned one on the mine's laws and on B by size.
EXE=$1; T="${RUN_DIR:-$TEMP}/held_prune"; R="$LOCALAPPDATA/claude-runs/tatic/2026-10-22"
mkdir -p "$T"; : > "$T/none.txt"
serve() { # fam rules laws -> free
  RULEMINER_FAMILY=$1 CHECK_FAMILY=$1 RULEMINER_DEEP3=1 MACHINE_BANNER=0 CHECK_RULES="$(cygpath -w "$2")" CHECK_LAWFILE="$(cygpath -w "$3")" \
    "$EXE" search::rule_set_kernel_check --exact --ignored --nocapture < /dev/null 2>&1 | awk '/^CHECKED/{f=$5; sub(/\(/,"",f); print f}'
}
fam_run() {
  fam=$1; L="$R-gen-warm-fix/mon_1/lib_$fam"; S="$R-size-band/size_band/$fam"; D="$T/$fam"; mkdir -p "$D/B"
  cat "$S/held_size_9.txt" "$S/held_size_11.txt" > "$D/A.txt"; IN="$L/laws_mine_ref.txt"
  SB_FAMILY=$fam SB_SALT=21 SB_PER=200 SB_OUT="$(cygpath -w "$D/B")" "$EXE" search::size_band_laws --exact --ignored --nocapture < /dev/null > "$D/B/gen.log" 2>&1
  cat "$D/A.txt" "$IN" "$L/laws_extra_ref.txt" > "$D/seen.txt"
  for k in 9 11; do grep -vxFf "$D/seen.txt" "$D/B/size_$k.txt" > "$D/B_$k.txt"; done
  for arm in held both; do
    cp "$L/rules.txt" "$D/$arm.txt"; a=$(serve $fam "$D/$arm.txt" "$D/A.txt"); in=$(serve $fam "$D/$arm.txt" "$IN")
    n=$(grep -c '' "$L/rules.txt")
    for i in $(seq "$n" -1 1); do
      rule=$(sed -n "${i}p" "$L/rules.txt"); grep -vxF -- "$rule" "$D/$arm.txt" > "$D/cand.txt"
      ca=$(serve $fam "$D/cand.txt" "$D/A.txt"); ok=0
      if [ "$ca" -ge "$a" ]; then
        if [ $arm = held ]; then ok=1; else ci=$(serve $fam "$D/cand.txt" "$IN"); [ "$ci" -ge "$in" ] && ok=1; fi
      fi
      if [ $ok = 1 ]; then mv "$D/cand.txt" "$D/$arm.txt"; a=$ca; [ $arm = both ] && in=$ci; echo "$fam $arm drop #$i (A $a): $rule"; fi
    done > "$D/$arm.log"
  done
  for rs in none full held both; do
    case $rs in none) f="$T/none.txt";; full) f="$L/rules.txt";; *) f="$D/$rs.txt";; esac
    echo "$fam $rs rules $(grep -c '' "$f") in $(serve $fam "$f" "$IN")/$(grep -c '' "$IN") A $(serve $fam "$f" "$D/A.txt")/$(grep -c '' "$D/A.txt") B9 $(serve $fam "$f" "$D/B_9.txt")/$(grep -c '' "$D/B_9.txt") B11 $(serve $fam "$f" "$D/B_11.txt")/$(grep -c '' "$D/B_11.txt")"
  done > "$D/score.txt"
}
for fam in add3 sbo3 mix3 cmp3d; do fam_run $fam & done; wait
cat "$T"/{add3,sbo3,mix3,cmp3d}/{held,both}.log; cat "$T"/{add3,sbo3,mix3,cmp3d}/score.txt
