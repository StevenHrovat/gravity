#!/usr/bin/env bash
# Attempt r3-1 (robust): build one target in the attempt's own WSL folder ~/formal-att-r3-1.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/attempts/r3-robust/build-r3-1.sh Attempts.R3.Robust
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-att-r3-1 bash sync-build.sh "$1" 2>&1 | grep -E "R3/(Robust|FlatFactors|TailDecay)|error|Build completed|build failed" | tail -${2:-60}
