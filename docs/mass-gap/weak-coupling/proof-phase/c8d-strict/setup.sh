#!/usr/bin/env bash
# c8d-strict: one-time build folder (copies the shared .lake so Mathlib and the existing modules are cached).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c8d-strict/setup.sh
set -e
mkdir -p ~/formal-c8d
if [ ! -d ~/formal-c8d/.lake ]; then cp -a ~/formal/.lake ~/formal-c8d/; fi
echo done
