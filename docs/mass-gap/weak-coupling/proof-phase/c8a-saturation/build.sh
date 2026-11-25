#!/usr/bin/env bash
# c8a-saturation: build one module in ~/formal-c9a.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c8a-saturation/build.sh ProofPhase.Saturation.<Module>
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c9a bash sync-build.sh "$1" > /tmp/c8a-build.log 2>&1
grep -v "^✔\|^info: \|Replayed\|^⣿\|Building\|^trace" /tmp/c8a-build.log | grep -A${2:-30} "^error\|Saturation.*warning\|warning: ProofPhase/Saturation\|Build completed\|error:" | head -${3:-120}
tail -3 /tmp/c8a-build.log
