#!/usr/bin/env bash
# r4-layer: build one module of Attempts.R4 in ~/formal-att-r4-2 only; full log in ~/formal-att-r4-2/build.log.
# Run: wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/attempts/r4-layer/build.sh Attempts.R4.LayerSector
set -u
DST="$HOME/formal-att-r4-2"
if [ ! -d "$DST/.lake" ]; then mkdir -p "$DST" && cp -a "$HOME/formal/.lake" "$DST/"; fi
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal && FORMAL_DST="$DST" bash sync-build.sh "$1" > "$DST/build.log" 2>&1
echo "exit: $?"
grep -n -A30 "^error: Attempts/R4\|^warning: Attempts/R4" "$DST/build.log" | head -200
grep -E "Build completed|build failed|^error" "$DST/build.log" | head -20
