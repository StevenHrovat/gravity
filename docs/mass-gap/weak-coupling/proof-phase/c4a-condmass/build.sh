#!/usr/bin/env bash
# c4a-condmass: sync the formal tree into ~/formal-c4a and build one target, e.g. ProofPhase.V3.Top
set -euo pipefail
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c4a bash sync-build.sh "${1:-ProofPhase.V3.Top}" 2>&1 | tail -n "${2:-80}"
