#!/usr/bin/env bash
# Workstream 2 (Route B): build one RouteB module in ~/formal-ws2 only.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/ws2-routeB/build.sh ProofPhase.RouteB.HankelRate
set -euo pipefail
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-ws2 bash sync-build.sh "${1:-ProofPhase.RouteB.HankelRate}" 2>&1 | grep -v "^✔\|^⣿\|^info: \|Replayed\|^Build completed" | tail -n 120
echo "exit: ${PIPESTATUS[0]}"
