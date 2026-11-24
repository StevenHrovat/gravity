#!/usr/bin/env bash
# Build one M1 module in the private folder:  bash build.sh <Module>   (e.g. Dilution)
# Full log: ~/formal-m1/build-<Module>.log; printed: errors with 30 lines of context, and the last line.
set -uo pipefail
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
log=~/formal-m1/build-$1.log
FORMAL_DST=~/formal-m1 bash sync-build.sh "ProofPhase.M1.$1" > "$log" 2>&1; rc=$?
grep -n -A30 '^error' "$log" | head -${2:-150}
tail -2 "$log"; echo "exit $rc"
