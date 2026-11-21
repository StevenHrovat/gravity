#!/usr/bin/env bash
# Copy the area-law project from the gravity checkout (Windows) to a Linux folder and build there (lake is slow on /mnt/c).
#   bash sync-build.sh [target]        default target: AreaLaw
set -euo pipefail
src=/mnt/c/claude/gravity-ym/docs/mass-gap/arealaw
dst=~/arealaw
mkdir -p "$dst/AreaLaw"
# The toolchain pin is stored as lean-toolchain.arealaw: gravity's setup check requires every file named lean-toolchain in the
# repository to pin gravity's own Lean (4.34.0), while this project builds on balaban-lean's Lean (4.35.0-rc2).
tr -d '\r' < "$src/lean-toolchain.arealaw" > "$dst/lean-toolchain"
for f in lakefile.toml AreaLaw.lean $(cd "$src" && ls AreaLaw/*.lean); do tr -d '\r' < "$src/$f" > "$dst/$f"; done
cd "$dst"
source ~/.elan/env
if [ ! -d .lake/packages/mathlib ]; then lake update && lake exe cache get; fi
lake build "${1:-AreaLaw}"
