#!/usr/bin/env bash
# Cycle 3, workstream 3 (c3c): create the private build folder ~/formal-c3c from the shared ~/formal (Mathlib cache).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c3c-certified/setup-c3c.sh
set -e
mkdir -p ~/formal-c3c
if [ ! -d ~/formal-c3c/.lake ]; then cp -a ~/formal/.lake ~/formal-c3c/; fi
ls ~/formal-c3c/.lake/packages | head
