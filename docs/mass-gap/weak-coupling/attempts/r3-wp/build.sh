#!/usr/bin/env bash
# Build the r3-wp Lean module in the attempt's own WSL folder (round-3 rules).
set -e
if [ ! -d ~/formal-att-r3-3/.lake ]; then mkdir -p ~/formal-att-r3-3 && cp -a ~/formal/.lake ~/formal-att-r3-3/; fi
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-att-r3-3 bash sync-build.sh Attempts.R3.WpNoise 2>&1 | tail -60
