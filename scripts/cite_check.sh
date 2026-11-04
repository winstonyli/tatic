#!/usr/bin/env bash
# Checks the doc-to-doc cites that tour_check.sh does not: section cites to docs/tier-cycle.md and RELATED_WORK.md (cite_check.pl),
# then the TOUR path#symbol cites (tour_check.sh). Exit 1 if either finds a broken cite. Run before moving or splitting a cited doc.
cd "$(dirname "$0")/.." || exit 2
rc=0
perl scripts/cite_check.pl . || rc=1
bash scripts/tour_check.sh || rc=1
exit $rc
