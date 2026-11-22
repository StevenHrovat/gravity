#!/usr/bin/env bash
# Build the FluxVac modules in ~/formal-c7a (cycle 7, workstream 1). Usage: bash build.sh [Module ...]
set -euo pipefail
if [ ! -d ~/formal-c7a/.lake ]; then mkdir -p ~/formal-c7a && cp -a ~/formal/.lake ~/formal-c7a/; fi
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
mods=("$@"); [ ${#mods[@]} -eq 0 ] && mods=(ProofPhase.FluxVac.Branches)
for m in "${mods[@]}"; do FORMAL_DST=~/formal-c7a bash sync-build.sh "$m" 2>&1 | grep -v "^⚠\|^✔\|linter\|^warning" | tail -80; done
