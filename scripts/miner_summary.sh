#!/usr/bin/env bash
# One summary line per rule-miner family (default mul shl lt; FAMILIES="shr" adds the 10-minute shr run): stragglers, covered, wall time, with CPU load and
# Defender state taken before the runs (LONG_RUNS.md). Pass env such as ABLATE=... through; MINER_EXE reuses a built test exe.
#
#   scripts/miner_summary.sh
#   ABLATE=ltself,ltzero,ltmax scripts/miner_summary.sh
set -euo pipefail
cd "$(dirname "$0")/.."
exe=${MINER_EXE:-$(cargo test --release --test church_bv --no-run 2>&1 | sed -n 's/.*(\(.*church_bv-[^)]*\.exe\)).*/\1/p' | tail -n1)}
cpu=$(powershell -NoProfile -Command "[int](Get-Counter '\Processor(_Total)\% Processor Time' -SampleInterval 2 -MaxSamples 2).CounterSamples[-1].CookedValue")
rtp=$(powershell -NoProfile -Command "(Get-MpComputerStatus).RealTimeProtectionEnabled")
echo "cpu=${cpu}% defender_rtp=${rtp} ablate=${ABLATE:-none} exe=${exe}"
powershell -NoProfile -Command "(Get-Process -Id $$ -ErrorAction SilentlyContinue) | Out-Null; (Get-Process -Id (Get-Process -Id \$PID).Id).PriorityClass='BelowNormal'" >/dev/null 2>&1 || true
export RULEMINER_ANY=${RULEMINER_ANY:-1} RULEMINER_ROUNDS=${RULEMINER_ROUNDS:-20}
for fam in ${FAMILIES:-mul shl lt}; do
  extra=""
  case $fam in
    mul) extra="MULMINER_MAX=${MULMINER_MAX:-5}" ;;
    shl) extra="RULEMINER_LAWS=${RULEMINER_LAWS:-300}" ;;
    lt) extra="RULEMINER_LAWS=${RULEMINER_LAWS:-150}" ;;
    shr) extra="RULEMINER_DEEP=1 MINER_SUB=1 RULEMINER_STRIDE=3 RULEMINER_LAWS=${RULEMINER_LAWS:-900}" ;;
  esac
  t0=$(date +%s)
  out=$(env RULEMINER_FAMILY=$fam $extra cmd //c start //wait //b //belownormal //affinity FFF "$exe" search::rule_miner --ignored --nocapture --exact 2>&1 || true)
  s=$(( $(date +%s) - t0 ))
  head=$(grep -m1 'stragglers of' <<<"$out" | sed "s/^RULEMINER [a-z]*: //")
  cov=$(grep -m1 'stragglers covered' <<<"$out" | sed "s/^RULEMINER [a-z]*: //")
  echo "$fam: ${head:-no header} | ${cov:-no coverage line} | ${s}s"
done
