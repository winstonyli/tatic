#!/bin/bash
# class_key.sh <exe>: classes::regenerate_key (plan docs/superpowers/plans/2026-10-23-class-table-normal-form.md, Task 2):
# refines the class table's key from the 8 tuples of 0s and 1s and writes tests/church_bv/class_key.txt on a clean round.
EXE=$1; T="${RUN_DIR:-$TEMP}"
"$EXE" classes::regenerate_key --exact --ignored --nocapture < /dev/null > "$T/class_key.log" 2>&1; rc=$?
grep -E "^(ROUND|WROTE)|panicked" "$T/class_key.log"
grep -E "^WROTE" "$T/class_key.log" | sed 's/^WROTE .* (/key /; s/)$//' > "$T/headline.txt"
exit $rc
