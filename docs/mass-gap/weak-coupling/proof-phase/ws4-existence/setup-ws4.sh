#!/usr/bin/env bash
# ws4: create the private build folder ~/formal-ws4 from the shared ~/formal (Mathlib cache).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/ws4-existence/setup-ws4.sh
set -e
mkdir -p ~/formal-ws4
if [ ! -d ~/formal-ws4/.lake ]; then cp -a ~/formal/.lake ~/formal-ws4/; fi
du -sh ~/formal-ws4/.lake | tail -1
