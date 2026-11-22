#!/usr/bin/env bash
# bash check.sh ProofPhase/Book/<File>.lean [lines] : sync ProofPhase to ~/formal-c6e, then elaborate that one file
# (its dependencies must already be built, see build.sh).
set -uo pipefail
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
dst=~/formal-c6e
for f in $(find ProofPhase -name '*.lean'); do mkdir -p "$dst/$(dirname "$f")"; tr -d '\r' < "$f" > "$dst/$f"; done
cd "$dst"; source ~/.elan/env
lake env lean "$1" 2>&1 | head -${2:-80}
