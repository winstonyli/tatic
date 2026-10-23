#!/bin/bash
# class_commit.sh <exe>: the class table's build commit (MB: commit, peak commit, working set) with mimalloc's large
# OS pages allowed and not (as sweep children run), before and after mi_collect(true) (plan Task 4, R9). The exe is the
# Task 4 build plus patches/class_commit.patch.
EXE=$1; T="${RUN_DIR:-$TEMP}"
for lp in 1 0; do
  MIMALLOC_ALLOW_LARGE_OS_PAGES=$lp "$EXE" classes::build_commit_probe --exact --ignored --nocapture < /dev/null > "$T/commit$lp.log" 2>&1
  echo "== large OS pages $lp: exit $?"; grep -E "^(COMMIT|CLASSES)|panicked" "$T/commit$lp.log"
done
grep -h "after mi_collect" "$T/commit0.log" > "$T/headline.txt"
