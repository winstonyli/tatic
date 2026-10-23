#!/bin/bash
# join_visit_trace.sh <exe>: why removing add3's ref rule 4 (`sub(x, xor(y, 0)) -> sub(x, y)`) frees 10 held-out laws
# (run 2026-10-22-rule-ablation), and how the free count on held-out laws moves with the join's budget. Serves the size-band's
# held-out laws of sizes 9 and 11 (run 2026-10-22-size-band, salt 11) under each family's salt-1 ref library (run
# 2026-10-22-gen-warm-fix, mon_1) at JOIN_VISIT 1000 (the default), 5000 and 20000; for add3 also without rule 4, and lists
# the laws that need a whole-term machine proof only with it at the default budget.
EXE=$1; T="${RUN_DIR:-$TEMP}/join_visit"; R="$LOCALAPPDATA/claude-runs/tatic/2026-10-22"
mkdir -p "$T"
serve() { # fam rules laws visit tag
  JOIN_VISIT=$4 RULEMINER_FAMILY=$1 CHECK_FAMILY=$1 RULEMINER_DEEP3=1 MACHINE_BANNER=0 CHECK_RULES="$(cygpath -w "$2")" CHECK_LAWFILE="$(cygpath -w "$3")" \
    "$EXE" search::rule_set_kernel_check --exact --ignored --nocapture < /dev/null > "$T/$5.log" 2>&1
  awk -v tag=$5 '/^CHECKED/{f=$5; sub(/\(/,"",f)} /^JOINED/{j=$2; s=$8; r=$11} /^NFSAME/{nf=$2} END{printf "%s: free %s joined %s nf-equal %s searches %s reached %s\n", tag, f, j, nf, s, r}' "$T/$5.log"
}
for fam in add3 sbo3 mix3 cmp3d; do
  L="$R-gen-warm-fix/mon_1/lib_$fam"; S="$R-size-band/size_band/$fam"
  cat "$S/held_size_9.txt" "$S/held_size_11.txt" > "$T/$fam.A.txt"
  [ $fam = add3 ] && sed 4d "$L/rules.txt" > "$T/add3.minus4.txt"
  for v in 1000 5000 20000; do
    serve $fam "$L/rules.txt" "$T/$fam.A.txt" $v "$fam-full-$v"
    [ $fam = add3 ] && serve $fam "$T/add3.minus4.txt" "$T/$fam.A.txt" $v "$fam-minus4-$v"
  done
done
echo "laws machine-proved only with add3's rule 4 at the default budget:"
diff <(grep '^MACHINE' "$T/add3-full-1000.log" | sort) <(grep '^MACHINE' "$T/add3-minus4-1000.log" | sort) | grep '^<' | sed 's/^< MACHINE 1 /  /'
