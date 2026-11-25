#!/usr/bin/env bash
# Build the DMP-native modules in ~/formal-c5e (cycle 5, workstream 5). Usage: bash build.sh [Module ...]
set -euo pipefail
if [ ! -d ~/formal-c5e/.lake ]; then mkdir -p ~/formal-c5e && cp -a ~/formal/.lake ~/formal-c5e/; fi
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
mods=("$@"); [ ${#mods[@]} -eq 0 ] && mods=(ProofPhase.DMP.Doubling ProofPhase.DMP.VacuumAct)
for m in "${mods[@]}"; do FORMAL_DST=~/formal-c5e bash sync-build.sh "$m"; done
