#!/usr/bin/env bash
# The local part of stage 1 of docs/paper/REVIEW.md: scrub scan and ledger check. Run from the repository root.
# The evidence gate (evidence/tools/check.sh), the axiom scripts and the independent re-check run in the Linux shell (REVIEW.md).
set -uo pipefail
cd "$(dirname "$0")/.."
rc=0
LC_ALL=C.UTF-8 bash tools/scrub-scan.sh || rc=1
PY=$(command -v python || command -v python3)
"$PY" tools/claims-check.py || rc=1
[ $rc -eq 0 ] && echo "paper-gate: OK" || echo "paper-gate: FAIL"
exit $rc
