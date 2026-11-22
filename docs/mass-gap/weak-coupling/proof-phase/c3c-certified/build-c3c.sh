#!/usr/bin/env bash
# Cycle 3, workstream 3 (c3c): build one target in ~/formal-c3c (one build at a time); prints errors only.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c3c-certified/build-c3c.sh ProofPhase.Certified.AdjointW
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c3c bash sync-build.sh "${1:-ProofPhase.Certified.AdjointW}" > /tmp/c3c-build.log 2>&1
grep -B2 -A14 "error: " /tmp/c3c-build.log | head -${2:-160}
grep -E "Build completed|build failed|declaration uses 'sorry'" /tmp/c3c-build.log | tail -5
