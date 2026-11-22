#!/usr/bin/env bash
# Build the Centre modules in ~/formal-c7b (c7b-centre). Usage: bash build.sh [Module ...]
set -euo pipefail
if [ ! -d ~/formal-c7b/.lake ]; then mkdir -p ~/formal-c7b && cp -a ~/formal/.lake ~/formal-c7b/; fi
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
mods=("$@"); [ ${#mods[@]} -eq 0 ] && mods=(ProofPhase.Centre.Ginibre ProofPhase.Centre.Comparison ProofPhase.Centre.Z2Wilson ProofPhase.Centre.Combined)
for m in "${mods[@]}"; do FORMAL_DST=~/formal-c7b bash sync-build.sh "$m" 2>&1 | grep -v "^⚠\|^✔\|linter\|^warning" | tail -80; done
