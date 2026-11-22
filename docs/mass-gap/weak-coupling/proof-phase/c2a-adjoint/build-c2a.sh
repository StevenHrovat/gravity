#!/usr/bin/env bash
# Cycle 2, workstream A: build one target in ~/formal-c2a (one build at a time); prints errors only.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c2a-adjoint/build-c2a.sh ProofPhase.Adjoint.TwoType
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c2a bash sync-build.sh "${1:-ProofPhase.Adjoint.TwoType}" > /tmp/c2a-build.log 2>&1
grep -B2 -A14 "error: " /tmp/c2a-build.log | head -${2:-160}
grep -E "Build completed|build failed|declaration uses 'sorry'" /tmp/c2a-build.log | tail -5
