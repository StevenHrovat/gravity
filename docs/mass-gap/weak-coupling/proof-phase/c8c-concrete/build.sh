#!/usr/bin/env bash
# c8c-concrete: build one module in ~/formal-c9c.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c8c-concrete/build.sh ProofPhase.OneBox2.<Module> [context lines]
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c9c bash sync-build.sh "$1" > /tmp/c8c-build.log 2>&1
echo "exit: $?"
grep -A${2:-14} "^error: " /tmp/c8c-build.log | head -${3:-150}
grep -n "sorry\|OneBox2.*warning: declaration\|Build completed" /tmp/c8c-build.log | head
