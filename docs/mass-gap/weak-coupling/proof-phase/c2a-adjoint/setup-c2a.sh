#!/usr/bin/env bash
# Cycle 2, workstream A (adjoint half): create the private build folder ~/formal-c2a from the shared ~/formal (Mathlib cache).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c2a-adjoint/setup-c2a.sh
set -e
mkdir -p ~/formal-c2a
if [ ! -d ~/formal-c2a/.lake ]; then cp -a ~/formal/.lake ~/formal-c2a/; fi
ls ~/formal-c2a/.lake/packages | head
