#!/usr/bin/env bash
# Build one module of the formal project in ~/formal-p4 (copy of ~/formal's .lake on first use).
set -euo pipefail
if [ ! -d ~/formal-p4/.lake ]; then mkdir -p ~/formal-p4 && cp -a ~/formal/.lake ~/formal-p4/; fi
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-p4 bash sync-build.sh "${1:-ProofPhase.Crossover.P4Chain}"
