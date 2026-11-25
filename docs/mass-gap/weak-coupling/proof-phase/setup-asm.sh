#!/usr/bin/env bash
# Proof phase, assembly: create the private build folder ~/formal-phase-asm from the shared ~/formal (Mathlib cache).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/setup-asm.sh
set -e
mkdir -p ~/formal-phase-asm
if [ ! -d ~/formal-phase-asm/.lake ]; then cp -a ~/formal/.lake ~/formal-phase-asm/; fi
ls ~/formal-phase-asm/.lake/packages | head
du -sh ~/formal-phase-asm/.lake | tail -1
