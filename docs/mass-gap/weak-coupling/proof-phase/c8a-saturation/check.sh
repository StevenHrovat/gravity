#!/usr/bin/env bash
# Quick check of one Saturation file (its imports must be built: build.sh first):
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c8a-saturation/check.sh Sheet
set -uo pipefail
f=ProofPhase/Saturation/$1.lean
mkdir -p ~/formal-c9a/ProofPhase/Saturation
tr -d '\r' < /mnt/c/claude/gravity-ym/docs/mass-gap/formal/$f > ~/formal-c9a/$f
cd ~/formal-c9a && source ~/.elan/env
lake env lean $f > /tmp/c8a-check.log 2>&1
grep -v "deprecated\|^Note: This linter\|linter\.\|^$" /tmp/c8a-check.log | grep -A ${2:-25} -E "^ProofPhase.*error" | head -${3:-200}
echo "check done: $(grep -c 'error' /tmp/c8a-check.log) error lines"
