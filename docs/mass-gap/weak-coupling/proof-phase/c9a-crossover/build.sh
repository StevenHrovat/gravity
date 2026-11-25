#!/usr/bin/env bash
# Build one module of the formal project in ~/formal-c9x (copy of ~/formal's .lake on first use).
set -euo pipefail
if [ ! -d ~/formal-c9x/.lake ]; then mkdir -p ~/formal-c9x && cp -a ~/formal/.lake ~/formal-c9x/; fi
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c9x bash sync-build.sh "${1:-ProofPhase.Crossover.Openness}"
