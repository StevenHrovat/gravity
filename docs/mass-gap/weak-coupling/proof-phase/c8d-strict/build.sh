#!/usr/bin/env bash
# c8d-strict: build one module in ~/formal-c8d.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c8d-strict/build.sh ProofPhase.Flip.Strict
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c8d bash sync-build.sh "${1:-ProofPhase.Flip.Strict}" 2>&1 | grep -v "^✔\|^info: \|Replayed\|^⣿\|Building\|^trace" | grep -A${2:-40} "^error\|Strict.*warning\|warning: ProofPhase/Flip/Strict\|Build completed" | head -${3:-200}
