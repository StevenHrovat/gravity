#!/usr/bin/env bash
# c4a-condmass: make the private build folder ~/formal-c4a from the shared Mathlib cache.
set -euo pipefail
mkdir -p ~/formal-c4a
if [ ! -d ~/formal-c4a/.lake ]; then cp -a ~/formal/.lake ~/formal-c4a/; fi
echo ok
