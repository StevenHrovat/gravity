#!/usr/bin/env bash
# Thread A, stage 1: the YM group's own runner on a fresh clone (integrity, build, review modules, tools, controls, Comparator).
# Run as user ym in the ym-replay distro. Writes everything under ~/ym-replay; the log of this script is stage1.log there.
set -uo pipefail
YM_COMMIT=b379615          # yang-mills-group/YM main as read on 2026-11-21
THREADS=${THREADS:-10}     # leaves room for the lattice runs on the Windows side
W=~/ym-replay
mkdir -p "$W" && cd "$W"
source ~/.elan/env
exec > >(tee -a "$W/stage1.log") 2>&1
echo "== stage 1 start $(date -u +%FT%TZ) on $(uname -srm), $(nproc) threads, $(free -g | awk '/Mem/{print $2}') GB, LEAN_NUM_THREADS=$THREADS"
[ -d YM ] || git clone -q https://github.com/yang-mills-group/YM.git
cd YM && git checkout -q "$YM_COMMIT" && echo "YM at $(git rev-parse HEAD)"
cd submissions/openai-20261028
export LEAN_NUM_THREADS=$THREADS
/usr/bin/time -v python3 scripts/verify.py integrity; echo "== integrity exit $?"
/usr/bin/time -v python3 scripts/verify.py all; echo "== all exit $?"
echo "== stage 1 end $(date -u +%FT%TZ)"
ls -d runs/*/ 2>/dev/null
find runs -maxdepth 2 -name result.json -exec sh -c 'echo "--- $1"; jq "{status, stage: .stage?}" "$1" 2>/dev/null || cat "$1"' _ {} \;
du -sh "$W" 2>/dev/null
