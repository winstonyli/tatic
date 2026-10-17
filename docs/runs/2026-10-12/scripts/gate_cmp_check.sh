# gate_cmp_check.sh: gate_cmp.sh on synthetic runs in <run dir, kk.sh>/gcc_check_{old,new}_{1,2}: an identical file, a reordered
# one, a changed one and one that differs only in a timing; prints "gate_cmp check ok" or the output it got, and removes the runs
d=$(dirname "$0"); k=$(bash "$d/kk.sh"); tag=gcc_check
for s in 1 2; do o=$k/${tag}_old_$s; n=$k/${tag}_new_$s; rm -rf $o $n; mkdir -p $o $n
  printf 'a\nb\n' > $o/same.txt; printf 'a\nb\n' > $n/same.txt
  printf 'a\nb\n' > $o/order.txt; printf 'b\na\n' > $n/order.txt
  printf 'a\n' > $o/changed.txt; printf 'c\n' > $n/changed.txt
  printf 'took 1.5s\n' > $o/time.log; printf 'took 2.25s\n' > $n/time.log
done
out=$(bash "$d/gate_cmp.sh" $tag); rm -rf $k/${tag}_*
want="salt 1: same file list (4 files)
DIFF salt 1 ./changed.txt
DIFF salt 1 ./order.txt (order only)
salt 2: same file list (4 files)
DIFF salt 2 ./changed.txt
DIFF salt 2 ./order.txt (order only)
cmp done"
[ "$out" = "$want" ] && echo "gate_cmp check ok" || { echo "gate_cmp check FAILED, got:"; echo "$out"; exit 1; }
