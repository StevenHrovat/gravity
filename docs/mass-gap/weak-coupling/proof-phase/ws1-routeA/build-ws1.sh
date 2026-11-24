#!/usr/bin/env bash
# Workstream 1 (Route A): build one target in ~/formal-ws1 (one build at a time); prints RouteA errors only.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/ws1-routeA/build-ws1.sh ProofPhase.RouteA.Blocking
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-ws1 bash sync-build.sh "${1:-ProofPhase.RouteA.Blocking}" > /tmp/ws1-build.log 2>&1
grep -B2 -A14 "error: " /tmp/ws1-build.log | head -${2:-160}
grep -E "Build completed|build failed|declaration uses 'sorry'" /tmp/ws1-build.log | tail -5
