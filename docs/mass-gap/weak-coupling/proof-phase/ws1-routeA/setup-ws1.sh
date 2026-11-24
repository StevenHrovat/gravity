#!/usr/bin/env bash
# Workstream 1 (Route A): create the private build folder ~/formal-ws1 from the shared ~/formal (Mathlib cache).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/ws1-routeA/setup-ws1.sh
set -e
mkdir -p ~/formal-ws1
if [ ! -d ~/formal-ws1/.lake ]; then cp -a ~/formal/.lake ~/formal-ws1/; fi
ls ~/formal-ws1/.lake/packages | head
ls ~/formal-ws1/.lake/build/lib/lean 2>/dev/null | head -20
