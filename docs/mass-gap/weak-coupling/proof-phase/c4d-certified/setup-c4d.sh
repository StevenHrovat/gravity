#!/usr/bin/env bash
# Cycle 4, workstream 4 (c4d): create the private build folder ~/formal-c4d from the shared ~/formal (Mathlib cache).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c4d-certified/setup-c4d.sh
set -e
mkdir -p ~/formal-c4d
if [ ! -d ~/formal-c4d/.lake ]; then cp -a ~/formal/.lake ~/formal-c4d/; fi
ls ~/formal-c4d/.lake/packages | head
