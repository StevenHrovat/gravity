#!/usr/bin/env bash
# c4b-seg1: make the private build folder ~/formal-c4b from the shared Mathlib cache.
set -euo pipefail
mkdir -p ~/formal-c4b
if [ ! -d ~/formal-c4b/.lake ]; then cp -a ~/formal/.lake ~/formal-c4b/; fi
echo ok
