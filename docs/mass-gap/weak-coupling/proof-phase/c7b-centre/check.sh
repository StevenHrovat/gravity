#!/usr/bin/env bash
# Quick check of one Centre file (imports already built): bash check.sh Ginibre [maxlines]
set -uo pipefail
f=ProofPhase/Centre/$1.lean
mkdir -p ~/formal-c7b/ProofPhase/Centre
tr -d '\r' < /mnt/c/claude/gravity-ym/docs/mass-gap/formal/$f > ~/formal-c7b/$f
cd ~/formal-c7b && source ~/.elan/env
lake env lean $f 2>&1 | grep -v "deprecated\|^Note: This linter\|linter\.\|^$" | head -${2:-150}
echo "check done"
