#!/usr/bin/env bash
# Build the r3-dmp Lean files in this attempt's own WSL folder (one build at a time).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/attempts/r3-dmp/build.sh [Module ...]
set -uo pipefail
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
mods=${*:-"DmpBridge DmpFlow DmpBalance DmpDuality"}
for m in $mods; do
  echo "=== Attempts.R3.$m"
  FORMAL_DST=~/formal-att-r3-5 bash sync-build.sh Attempts.R3.$m 2>&1 | grep -v "^trace:" | grep -E -A12 "error|R3.|Build completed|sorry" | tail -80
done
