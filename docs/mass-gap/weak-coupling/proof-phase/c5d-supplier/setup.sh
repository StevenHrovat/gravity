#!/usr/bin/env bash
# c5d-supplier: private build folder ~/formal-c5d from the shared Mathlib cache.
set -euo pipefail
mkdir -p ~/formal-c5d
if [ ! -d ~/formal-c5d/.lake ]; then cp -a ~/formal/.lake ~/formal-c5d/; fi
echo ok
