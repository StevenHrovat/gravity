#!/usr/bin/env bash
# One-time: private build folder for the M1 tools (copy of the shared .lake cache).
set -euo pipefail
if [ ! -d ~/formal-m1/.lake ]; then mkdir -p ~/formal-m1 && cp -a ~/formal/.lake ~/formal-m1/; fi
du -sh ~/formal-m1 | tail -1
