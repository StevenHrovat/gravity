#!/usr/bin/env bash
# c8a-saturation: one-time build folder (copies the shared .lake so Mathlib and the existing modules are cached).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c8a-saturation/setup.sh
set -e
mkdir -p ~/formal-c9a
if [ ! -d ~/formal-c9a/.lake ]; then cp -a ~/formal/.lake ~/formal-c9a/; fi
du -sh ~/formal-c9a/.lake
echo done
