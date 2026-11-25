#!/usr/bin/env bash
# Build one module of the formal project in ~/formal-dy (copy of ~/formal's .lake on first use).
set -euo pipefail
if [ ! -d ~/formal-dy/.lake ]; then mkdir -p ~/formal-dy && cp -a ~/formal/.lake ~/formal-dy/; fi
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-dy bash sync-build.sh "${1:-ProofPhase.Crossover.Dichotomy}"
