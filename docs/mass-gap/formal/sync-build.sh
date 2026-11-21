#!/usr/bin/env bash
# Copy the formal project from the gravity checkout (Windows) to a Linux folder and build there (lake is slow on /mnt/c).
#   bash sync-build.sh [target]        default target: AreaLaw
# Lean 4.34.0 (gravity's baseline, lean-toolchain) with Mathlib v4.34.0. Target folder: $FORMAL_DST, default ~/formal.
set -euo pipefail
src=/mnt/c/claude/gravity-ym/docs/mass-gap/formal
dst=${FORMAL_DST:-~/formal}
mkdir -p "$dst"
cd "$src"
for f in lean-toolchain lakefile.toml $(ls *.lean) $(find AreaLaw Influence Positivity OneScale Attempts -name '*.lean' 2>/dev/null); do
  mkdir -p "$dst/$(dirname "$f")"; tr -d '\r' < "$f" > "$dst/$f"
done
cd "$dst"
source ~/.elan/env
if [ ! -d .lake/packages/mathlib ]; then lake update && lake exe cache get; fi
lake build "${1:-AreaLaw}"
