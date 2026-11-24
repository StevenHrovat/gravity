#!/usr/bin/env bash
# c3d-h1: sync the formal tree into ~/formal-c3d and build one target, e.g. ProofPhase.H1.Level
set -euo pipefail
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c3d bash sync-build.sh "${1:-ProofPhase.H1.Level}" 2>&1 | tail -n "${2:-60}"
