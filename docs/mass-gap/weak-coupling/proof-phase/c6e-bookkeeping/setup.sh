#!/usr/bin/env bash
set -euo pipefail
mkdir -p ~/formal-c6e
if [ ! -d ~/formal-c6e/.lake ]; then cp -a ~/formal/.lake ~/formal-c6e/; fi
ls ~/formal-c6e
