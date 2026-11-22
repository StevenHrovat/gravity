#!/usr/bin/env bash
# Cycle 2, workstream C (torus decay, assembly upkeep): private build folder ~/formal-c2c from ~/formal (Mathlib cache).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c2c-torus/setup.sh
set -e
mkdir -p ~/formal-c2c
if [ ! -d ~/formal-c2c/.lake ]; then cp -a ~/formal/.lake ~/formal-c2c/; fi
ls ~/formal-c2c/.lake/packages | head
du -sh ~/formal-c2c/.lake | tail -1
