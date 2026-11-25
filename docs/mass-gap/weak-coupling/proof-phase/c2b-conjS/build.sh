#!/usr/bin/env bash
# Build one module of ProofPhase.SectorS in this workstream's own WSL folder (~/formal-c2b).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c2b-conjS/build.sh ProofPhase.SectorS.GeneratorRate
set -euo pipefail
if [ ! -d ~/formal-c2b/.lake ]; then mkdir -p ~/formal-c2b && cp -a ~/formal/.lake ~/formal-c2b/; fi
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c2b bash sync-build.sh "$1" 2>&1 | grep -v "^✔\|^⣿\|^info: \[" | awk "/SectorS|^error|unsolved|⊢|Build completed/{p=1} p" | grep -v "^warning: (AreaLaw|OneScale|Positivity|Attempts|Influence)" | tail -60
