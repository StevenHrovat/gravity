#!/usr/bin/env bash
# Cycle 4, workstream 3 (c4c-seg2): sync and build one target in ~/formal-c4c (one build at a time); prints errors only.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c4c-seg2/build.sh ProofPhase.Seg2.Filter
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c4c bash sync-build.sh "$1" > /tmp/c4c-build.log 2>&1
grep -A14 "error: " /tmp/c4c-build.log | head -200
grep -E "Build completed|build failed|declaration uses 'sorry'" /tmp/c4c-build.log | tail -8
