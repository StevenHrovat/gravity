#!/usr/bin/env bash
# c3d-h1: make the private build folder ~/formal-c3d from the shared Mathlib cache.
set -euo pipefail
mkdir -p ~/formal-c3d
if [ ! -d ~/formal-c3d/.lake ]; then cp -a ~/formal/.lake ~/formal-c3d/; fi
echo ok
