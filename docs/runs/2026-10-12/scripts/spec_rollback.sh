# usage: spec_rollback.sh <exe> [<baseline exe>]: an add3 ref mine (RULEMINER_FAST=1, salt 1) offered false but attractive
# candidates (RULEMINER_EXTRA), so winners fail their proofs: main-path rounds roll back and lookahead plays again; prints the failed
# proofs and the chosen rules, and with a baseline exe (one proving winners in turn) diffs the chosen rules against its own
k=$(bash "$(dirname "$0")/kk.sh")/spec_rollback; rm -rf $k; mkdir -p $k
# the first three win main-path rounds; the last four win only on lookahead's greedy paths, which then play again
printf 'sub(x, y) -> x\nadd(x, y) -> x\nadd(add(x, y), z) -> add(x, z)\nsub(add(x, y), z) -> add(x, z)\nsub(x, add(y, z)) -> sub(x, y)\nadd(sub(x, y), z) -> sub(z, y)\nsub(sub(x, y), z) -> sub(x, z)\n' > $k/false.rules
run() { out=$k/$1; mkdir -p $out
  MACHINE_STATE=0 LOOP_MODE=ref LOOP_OUT=$(cygpath -w $out) FAMILY=add3 B=100 K=1 RULEMINER_FAST=1 RULEMINER_SHUFFLE=1 \
    RULEMINER_EXTRA=$(cygpath -w $k/false.rules) "$2" driver::loop_stream --exact --ignored --nocapture > $out/log.txt 2>&1
  grep -h "RULEMINER chosen" $out/mine_*.log | sed 's/^.*: //' > $out/chosen.txt; }
run new "$1"; grep -h "lazy proofs\|rolled back\|played again" $k/new/mine_*.log; echo "chosen: $(wc -l < $k/new/chosen.txt)"
if [ -n "$2" ]; then run base "$2"; diff $k/base/chosen.txt $k/new/chosen.txt && echo "chosen rules identical"; fi
