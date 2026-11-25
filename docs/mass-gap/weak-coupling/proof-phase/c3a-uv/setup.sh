#!/usr/bin/env bash
# Cycle 3, workstream 1 (c3a-uv): private build folder ~/formal-c3a from ~/formal (Mathlib cache).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c3a-uv/setup.sh
set -e
mkdir -p ~/formal-c3a
if [ ! -d ~/formal-c3a/.lake ]; then cp -a ~/formal/.lake ~/formal-c3a/; fi
ls ~/formal-c3a/.lake/packages | head
du -sh ~/formal-c3a/.lake | tail -1
