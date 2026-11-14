#!/usr/bin/env bash
# Checks the doc-to-doc cites that tour_check.sh does not: section and § cites to docs/tier-cycle/ and docs/related-work/ (cite_check.pl),
# backticked repo paths that no longer exist (path_cite_check.pl), then the TOUR path#symbol cites (tour_check.sh). Exit 1 if any
# finds a broken cite. Run before moving, splitting or deleting a cited file.
cd "$(dirname "$0")/../.." || exit 2
rc=0
perl scripts/check/cite_check.pl . || rc=1
perl scripts/check/path_cite_check.pl . || rc=1
bash scripts/check/tour_check.sh || rc=1
exit $rc
