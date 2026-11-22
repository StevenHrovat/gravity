#!/usr/bin/env bash
# Cycle 2, workstream C: sync and build one or more targets in ~/formal-c2c (one build at a time); prints errors only.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c2c-torus/build.sh ProofPhase.Torus.Assembly [more targets]
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c2c bash sync-build.sh "$1" > /tmp/c2c-build.log 2>&1
shift
if [ $# -gt 0 ]; then (cd ~/formal-c2c && source ~/.elan/env && lake build "$@") >> /tmp/c2c-build.log 2>&1; fi
grep -A14 "error: " /tmp/c2c-build.log | head -200
grep -E "Build completed|build failed|declaration uses 'sorry'" /tmp/c2c-build.log | tail -8
