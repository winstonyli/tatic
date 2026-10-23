#!/bin/bash
# class_held.sh <exe>: classes::held_out_replacements_prove (plan docs/superpowers/plans/2026-10-23-class-table-normal-form.md, Task 4):
# canonicalizes the held-out laws (docs/runs/2026-10-23/fixtures/held), checks every replacement has a verdict at width 4
# and compiles every law that meets to a kernel-checked proof.
EXE=$1; T="${RUN_DIR:-$TEMP}"
"$EXE" classes::held_out_replacements_prove --exact --ignored --nocapture < /dev/null > "$T/class_held.log" 2>&1; rc=$?
grep -E "^(CLASSES|LAWS|REPLACEMENTS|CLASS_UNUSABLE)|panicked" "$T/class_held.log"
grep -E "^REPLACEMENTS" "$T/class_held.log" > "$T/headline.txt"
exit $rc
