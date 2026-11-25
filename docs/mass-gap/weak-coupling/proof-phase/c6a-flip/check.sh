#!/usr/bin/env bash
# Quick check of one Flip file (after build.sh has built its imports): bash check.sh Bound
set -uo pipefail
f=ProofPhase/Flip/$1.lean
mkdir -p ~/formal-c6a/ProofPhase/Flip
tr -d '\r' < /mnt/c/claude/gravity-ym/docs/mass-gap/formal/$f > ~/formal-c6a/$f
cd ~/formal-c6a && source ~/.elan/env
lake env lean $f 2>&1 | grep -v "deprecated\|^Note: This linter\|linter\.\|^$" | grep -B2 -A 30 -E "^ProofPhase.*error" | head -${2:-150}
echo "check done"
