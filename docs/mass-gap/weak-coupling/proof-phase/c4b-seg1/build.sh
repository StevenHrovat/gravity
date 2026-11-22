#!/usr/bin/env bash
# c4b-seg1: sync the formal tree into ~/formal-c4b and build one target, e.g. ProofPhase.Seg1.Envelope
set -euo pipefail
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c4b bash sync-build.sh "${1:-ProofPhase.Seg1.Envelope}" 2>&1 | tail -n "${2:-80}"
