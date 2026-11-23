#!/usr/bin/env bash
# c9b-adjoint: build one module in ~/formal-c9y (one-time: mkdir -p ~/formal-c9y && cp -a ~/formal/.lake ~/formal-c9y/).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c9b-adjoint/build.sh ProofPhase.Adjoint2.Transfer
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c9y bash sync-build.sh "${1:-ProofPhase.Adjoint2.Transfer}" 2>&1 | tail -60
