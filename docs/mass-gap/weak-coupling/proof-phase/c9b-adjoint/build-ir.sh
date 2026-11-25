#!/usr/bin/env bash
# c9b round 2 (infrared): build one module in ~/formal-ir (created here from ~/formal/.lake if missing).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c9b-adjoint/build-ir.sh ProofPhase.Adjoint2.CostCoupling
if [ ! -d ~/formal-ir/.lake ]; then mkdir -p ~/formal-ir && cp -a ~/formal/.lake ~/formal-ir/; fi
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-ir bash sync-build.sh "${1:-ProofPhase.Adjoint2.Transfer}" 2>&1 | tail -80
