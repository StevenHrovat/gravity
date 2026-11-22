#!/usr/bin/env bash
# Build the flip modules in ~/formal-c6a (cycle 6, workstream 1). Usage: bash build.sh [Module ...]
set -euo pipefail
if [ ! -d ~/formal-c6a/.lake ]; then mkdir -p ~/formal-c6a && cp -a ~/formal/.lake ~/formal-c6a/; fi
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
mods=("$@"); [ ${#mods[@]} -eq 0 ] && mods=(ProofPhase.Flip.Bound ProofPhase.Flip.Floor)
for m in "${mods[@]}"; do FORMAL_DST=~/formal-c6a bash sync-build.sh "$m" 2>&1 | grep -v "^⚠\|^✔\|linter\|^warning" | tail -60; done
