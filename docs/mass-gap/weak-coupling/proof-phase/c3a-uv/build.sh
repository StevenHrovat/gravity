#!/usr/bin/env bash
# Cycle 3, workstream 1 (c3a-uv): sync and build one target in ~/formal-c3a (one build at a time); prints errors only.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c3a-uv/build.sh ProofPhase.UV.Split
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c3a bash sync-build.sh "$1" > /tmp/c3a-build.log 2>&1
grep -A14 "error: " /tmp/c3a-build.log | head -150
grep -E "Build completed|build failed|declaration uses 'sorry'" /tmp/c3a-build.log | tail -8
