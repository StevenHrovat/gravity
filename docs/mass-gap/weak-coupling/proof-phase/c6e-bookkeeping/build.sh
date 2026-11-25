#!/usr/bin/env bash
# bash build.sh ProofPhase.Book.<Module> [tail-lines]
set -uo pipefail
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c6e bash sync-build.sh "$1" 2>&1 | grep -v "^✔\|^⣿\|Replayed\|^info: \[" | tail -${2:-80}
