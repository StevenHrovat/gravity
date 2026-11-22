#!/usr/bin/env bash
# Workstream 1: elaborate a scratch Lean file (given as a Windows-side path) against ~/formal-ws1 (imports must be built).
#   wsl -d ym-replay -u ym -- bash /mnt/c/.../ws1-routeA/probe-ws1.sh /mnt/c/.../probe.lean
cd ~/formal-ws1
source ~/.elan/env
tr -d '\r' < "$1" > /tmp/ws1-probe.lean
timeout 900 lake env lean /tmp/ws1-probe.lean 2>&1 | head -${2:-80}
