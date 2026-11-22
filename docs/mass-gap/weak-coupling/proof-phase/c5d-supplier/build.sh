#!/usr/bin/env bash
# c5d-supplier: sync the formal tree into ~/formal-c5d and build one target, e.g. ProofPhase.Defects.Annealed
set -euo pipefail
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c5d bash sync-build.sh "${1:-ProofPhase.Defects.Annealed}" 2>&1 | tail -n "${2:-80}"
