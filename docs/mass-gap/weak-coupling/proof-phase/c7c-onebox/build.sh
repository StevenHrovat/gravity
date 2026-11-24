#!/usr/bin/env bash
# c7c-onebox: build one module in ~/formal-c8a.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c7c-onebox/build.sh ProofPhase.OneBox.<Module>
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c8a bash sync-build.sh "$1" 2>&1 | grep -v "^✔\|^info: \|Replayed\|^⣿\|Building\|^trace" | grep -A${2:-40} "^error\|OneBox.*warning\|warning: ProofPhase/OneBox\|Build completed" | head -150
