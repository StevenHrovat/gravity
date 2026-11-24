#!/usr/bin/env bash
# ws4: build one target in ~/formal-ws4 (one build at a time); prints errors in ProofPhase only.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/ws4-existence/build-ws4.sh ProofPhase.Existence.Bridge
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-ws4 bash sync-build.sh "${1:-ProofPhase.Existence.Bridge}" > /tmp/ws4-build.log 2>&1
grep -B2 -A14 "error: " /tmp/ws4-build.log | grep -v "^warning" | head -${2:-160}
grep -E "Build completed|build failed|declaration uses 'sorry'" /tmp/ws4-build.log | tail -5
