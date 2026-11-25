#!/usr/bin/env bash
# One-time: copy the built .lake of ~/formal into the private build folder ~/formal-c5c.
set -euo pipefail
mkdir -p ~/formal-c5c
if [ ! -d ~/formal-c5c/.lake ]; then cp -a ~/formal/.lake ~/formal-c5c/; fi
ls ~/formal-c5c
