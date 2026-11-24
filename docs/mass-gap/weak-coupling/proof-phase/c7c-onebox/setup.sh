#!/usr/bin/env bash
# c7c-onebox: one-time build folder (copies the shared .lake so Mathlib and the existing modules are cached).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c7c-onebox/setup.sh
set -e
mkdir -p ~/formal-c8a
if [ ! -d ~/formal-c8a/.lake ]; then cp -a ~/formal/.lake ~/formal-c8a/; fi
echo done
