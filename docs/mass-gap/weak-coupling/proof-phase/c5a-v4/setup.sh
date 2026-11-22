#!/usr/bin/env bash
# c5a-v4: make the private build folder ~/formal-c5a from the shared Mathlib cache.
set -euo pipefail
mkdir -p ~/formal-c5a
if [ ! -d ~/formal-c5a/.lake ]; then cp -a ~/formal/.lake ~/formal-c5a/; fi
echo ok
