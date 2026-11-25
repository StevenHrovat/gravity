#!/usr/bin/env bash
# c5a-v4: sync the formal tree into ~/formal-c5a and build one target, e.g. ProofPhase.V4.Top
set -euo pipefail
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c5a bash sync-build.sh "${1:-ProofPhase.V4.Top}" 2>&1 | tail -n "${2:-80}"
