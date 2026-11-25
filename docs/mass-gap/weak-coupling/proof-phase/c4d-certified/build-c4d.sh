#!/usr/bin/env bash
# Cycle 4, workstream 4 (c4d): build one target in ~/formal-c4d (one build at a time); prints errors only.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c4d-certified/build-c4d.sh ProofPhase.Certified.Measured
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c4d bash sync-build.sh "${1:-ProofPhase.Certified.Measured}" > /tmp/c4d-build.log 2>&1
grep -B2 -A14 "error: " /tmp/c4d-build.log | head -${2:-160}
grep -E "Build completed|build failed|declaration uses 'sorry'" /tmp/c4d-build.log | tail -5
