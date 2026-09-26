#!/usr/bin/env bash
# Runnable check for clean.py (scripts/quiet_ab/test_clean.sh): short runs get samples; a run's own CPU is
# subtracted; selfplay, load, and failure make a run dirty; old 4-column
# logs still parse. Also pin.sh: a relative exe path with a directory runs,
# and the child's exit code and cpu= line come back.
cd "$(dirname "$0")"; t=$(mktemp -d); export AB_CORES=16
# 102: 12% total. 104: 30%. 106: selfplay. 110: 30%.
printf '100 10.0 0\n102 12.0 0\n104 30.0 0\n106 10.0 1\n110 30.0 0\n200 9.0 0\n' > $t/s
# A1: sample 102 only, no own load: foreign 12, clean.
# B1: sample 104, own 0.32 s = 1% of 16 cores over 2 s: foreign 29, dirty.
# A2: sample 106 has selfplay: dirty.  B2: no samples: dirty.
# A3: rc=1: dirty.
# B3: sample 110 at 30%, own 4 s = 12.5%: foreign 17.5, clean.
printf 'run A 1 101 101 rc=0 cpu=0\nrun B 1 103 103 rc=0 cpu=0.32\nrun A 2 105 105 rc=0 cpu=0\nrun B 2 150 151 rc=0 cpu=0\nrun A 3 101 101 rc=1 cpu=0\nrun B 3 109 109 rc=0 cpu=4\n' > $t/r
got=$(python clean.py $t/s $t/r | awk '{print $1 $2 ":" $3}' | tr '\n' ' ')
want='A1:clean B1:dirty A2:dirty B2:dirty A3:dirty B3:clean '
[ "$got" = "$want" ] || { echo "FAIL new: $got"; exit 1; }
printf '100 10.0 2.0 0\n102 40.0 2.0 0\n' > $t/s4; printf 'run A 1 101 101 rc=0\n' > $t/r4
got=$(python clean.py $t/s4 $t/r4 | awk '{print $3}')
[ "$got" = dirty ] || { echo "FAIL old: $got"; exit 1; }
mkdir -p $t/bin && cp /c/Windows/System32/where.exe $t/bin/
out=$(cd $t && "$OLDPWD/pin.sh" bin/where.exe where.exe); rc=$?
[ $rc = 0 ] && [ "${out##*cpu=}" != "$out" ] || { echo "FAIL pin: rc=$rc $out"; exit 1; }
echo PASS
