#!/usr/bin/env bash
# c9b CPU pilot (PREREG-PILOT.md). DO NOT RUN before the owner's explicit OK. One check at a time; each check under 30 minutes.
#   bash run_pilot.sh E1 | E2 | P        (Git Bash, from this folder; Windows Python `py` with numpy)
set -u
cd "$(dirname "$0")"
case "${1:-}" in
  E1)
    # run 1 (FAILED, kept): --nboot 30 --seed 20261124 --out pilot_E1.json
    # run 2 (FAILED, kept; amendment 1): --error bootstrap --nboot 200 --seed 20261125 --out pilot_E1_run2.json
    # run 3 (amendment 2): jackknife over K = 20 independent replicas, seed 20261126
    timeout 1800 py ir_condlaw.py exactcheck --go --n 250000 --reps 10 --error replica --K 20 --seed 20261126 --out pilot_E1_run3.json > pilot_E1_run3.log 2>&1 ;;
  C1)
    # amendment 4: calibration of the U-statistic floor on exact i.i.d. samples
    timeout 1800 py ir_condlaw.py calib1 --go --draws 200 --K 8 --nr 980 --seed 20261127 --out pilot_C1.json > pilot_C1.log 2>&1 ;;
  E2)
    # run 1 (FAILED, kept): seeds 11-15, outputs pilot_E2a-e.npz, pilot_E2.log. Run 2 (FAILED, kept; amendment 3): seeds 111-115,
    # pilot_E2r2*. Run 3 (amendment 4): seeds 211-215, pilot_E2r3*.
    common="run --go --action fit280 --N 4 --n 0 --R 2 --B 16 --x 0,0,0,0,1 --y 0,0,0,0,2 --background flat --pin-mass       --ntherm 30 --ntraj 600 --eps 0.05 --nleap 20 --max-wall 330"
    py ir_constrained.py $common --kappa 200 --move none --seed 211 --out pilot_E2r3a.npz  > pilot_E2r3.log 2>&1
    py ir_constrained.py $common --kappa 200 --move flip --seed 212 --out pilot_E2r3b.npz >> pilot_E2r3.log 2>&1
    py ir_constrained.py $common --kappa 800 --move none --seed 213 --out pilot_E2r3c.npz >> pilot_E2r3.log 2>&1
    py ir_constrained.py $common --kappa 800 --move flip --seed 214 --out pilot_E2r3d.npz >> pilot_E2r3.log 2>&1
    py ir_constrained.py $common --kappa 800 --move none --seed 215 --out pilot_E2r3e.npz >> pilot_E2r3.log 2>&1
    for p in "a b" "c d" "c e"; do set -- $p
      py ir_condlaw.py analyse pilot_E2r3$1.npz pilot_E2r3$2.npz --error replica --exact-flat --d2 --null-q >> pilot_E2r3.log 2>&1
    done ;;
  P)
    common="run --go --action wilson --beta 0.5 --N 8 --n 1 --R 2 --B 1 --x 0,0,0,0,1 --y 0,0,0,0,2 --background typical \
      --bgseed 1000 --npre 30 --nanneal 20 --ntherm 20 --ntraj 150 --eps 0.05 --nleap 10 --kappa 100 --max-wall 600"
    py ir_constrained.py $common --move none --seed 21 --out pilot_Pa.npz  > pilot_P.log 2>&1
    py ir_constrained.py $common --move flip --seed 22 --out pilot_Pb.npz >> pilot_P.log 2>&1
    py ir_constrained.py $common --move none --seed 23 --out pilot_Pc.npz >> pilot_P.log 2>&1
    for p in "a b" "a c"; do set -- $p
      py ir_condlaw.py analyse pilot_P$1.npz pilot_P$2.npz --error replica --nblock 5 --d2 >> pilot_P.log 2>&1
    done ;;
  *) echo "usage: bash run_pilot.sh E1|C1|E2|P  (only after the owner's OK; PREREG-PILOT.md)"; exit 2 ;;
esac
