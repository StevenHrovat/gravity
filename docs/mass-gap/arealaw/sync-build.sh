#!/usr/bin/env bash
# Copy the area-law project from the gravity checkout (Windows) to a Linux folder and build there (lake is slow on /mnt/c).
#   bash sync-build.sh [target]        default target: AreaLaw
set -euo pipefail
src=/mnt/c/claude/gravity-ym/docs/mass-gap/arealaw
dst=~/arealaw
mkdir -p "$dst/AreaLaw"
for f in lean-toolchain lakefile.toml AreaLaw.lean $(cd "$src" && ls AreaLaw/*.lean); do tr -d '\r' < "$src/$f" > "$dst/$f"; done
cd "$dst"
source ~/.elan/env
if [ ! -d .lake/packages/mathlib ]; then lake update && lake exe cache get; fi
lake build "${1:-AreaLaw}"
