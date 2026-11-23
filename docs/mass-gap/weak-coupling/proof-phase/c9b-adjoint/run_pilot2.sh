#!/usr/bin/env bash
# c9b pilot 2: the tuning pre-step only (PREREG-PILOT2.md). CPU; one setting at a time; 30-minute cap each.
#   bash run_pilot2.sh TA | TB
set -u
cd "$(dirname "$0")"
case "${1:-}" in
  TA) timeout 1800 py ir_constrained.py tune --go --precond --beta 0.5 --N 8 --n 1 --kappas 10,20,40 --npre 100 --n-meas 40 \
        --seed 41 --bgseed 4000 --max-wall 1500 --out pilot2_TA.json > pilot2_TA.log 2>&1 ;;
  TB) timeout 1800 py ir_constrained.py tune --go --precond --beta 2.3 --N 16 --n 2 --kappas 10,40 --npre 100 --n-meas 30 \
        --seed 42 --bgseed 4001 --max-wall 1500 --out pilot2_TB.json > pilot2_TB.log 2>&1 ;;
  TBp) timeout 1800 py ir_constrained.py tune --go --precond --beta 2.3 --N 12 --n 2 --kappas 10 --npre 100 --n-meas 30         --seed 43 --bgseed 4002 --max-wall 1500 --out pilot2_TBp.json > pilot2_TBp.log 2>&1 ;;
  *) echo "usage: bash run_pilot2.sh TA|TB|TBp  (PREREG-PILOT2.md)"; exit 2 ;;
esac
