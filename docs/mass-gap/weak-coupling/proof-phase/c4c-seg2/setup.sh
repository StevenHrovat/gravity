#!/usr/bin/env bash
# Cycle 4, workstream 3 (c4c-seg2): private build folder ~/formal-c4c from ~/formal (Mathlib cache).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c4c-seg2/setup.sh
set -e
mkdir -p ~/formal-c4c
if [ ! -d ~/formal-c4c/.lake ]; then cp -a ~/formal/.lake ~/formal-c4c/; fi
ls ~/formal-c4c/.lake/packages | head
du -sh ~/formal-c4c/.lake | tail -1
