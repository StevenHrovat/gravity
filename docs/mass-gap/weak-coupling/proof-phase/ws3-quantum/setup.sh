#!/usr/bin/env bash
# ws3-quantum: create the private build folder ~/formal-ws3 from the shared ~/formal (Mathlib cache and built oleans).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/ws3-quantum/setup.sh
set -e
mkdir -p ~/formal-ws3
if [ ! -d ~/formal-ws3/.lake ]; then cp -a ~/formal/.lake ~/formal-ws3/; fi
ls ~/formal-ws3/.lake/packages | head
du -sh ~/formal-ws3/.lake | tail -1
