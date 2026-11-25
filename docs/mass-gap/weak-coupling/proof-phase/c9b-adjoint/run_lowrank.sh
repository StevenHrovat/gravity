#!/usr/bin/env bash
# c9b option B (PILOT2.md, owner "Yes, build B"): CG count (data-free), agreement check, T-B' with B. CPU; 30-minute caps.
set -u
cd "$(dirname "$0")"
case "${1:-}" in
  CG4) timeout 1800 py ir_lowrank.py cgcount --go --settings 12,2 --nrhs 3 --out cgcount_b4.json > cgcount_b4.log 2>&1 ;;
  CG8) timeout 1800 py ir_lowrank.py cgcount --go --settings 24,3 --nrhs 1 --out cgcount_b8.json > cgcount_b8.log 2>&1 ;;
  AGREE) timeout 1800 py ir_lowrank.py agree --go --out agree_lowrank.json > agree_lowrank.log 2>&1 ;;
  TBpB) timeout 1800 py ir_lowrank.py tune --go --out pilot2_TBpB.json > pilot2_TBpB.log 2>&1 ;;
  *) echo "usage: bash run_lowrank.sh CG4|CG8|AGREE|TBpB"; exit 2 ;;
esac
