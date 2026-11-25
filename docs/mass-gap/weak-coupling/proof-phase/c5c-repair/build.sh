#!/usr/bin/env bash
# Build one module of formal/ProofPhase/Repair in ~/formal-c5c.  bash build.sh ProofPhase.Repair.<Module>
set -uo pipefail
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c5c bash sync-build.sh "$1" 2>&1 | grep -v "^✔\|^⣿\|Replayed\|^info: \[" | tail -${2:-80}
