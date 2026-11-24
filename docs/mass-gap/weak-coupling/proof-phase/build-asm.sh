#!/usr/bin/env bash
# Proof phase, assembly: build one target in ~/formal-phase-asm (one build at a time); prints ProofPhase errors only.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/build-asm.sh ProofPhase.Assembly
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-phase-asm bash sync-build.sh "${1:-ProofPhase.Assembly}" > /tmp/asm-build.log 2>&1
grep -A12 "error: ProofPhase" /tmp/asm-build.log | head -${2:-150}
grep -E "Build completed|build failed|sorry" /tmp/asm-build.log | tail -5
