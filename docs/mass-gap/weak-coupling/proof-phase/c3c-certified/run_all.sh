#!/usr/bin/env bash
# PREREG run 3, serial queue (one process at a time): window at -0.22; tight suprema at |b_A| = 0.05 ... 0.2 (both signs),
# target = float supremum * 1.02 (explore: +0.05 0.07101, +0.1 0.07971, +0.15 0.08834, +0.2 0.09662; -0.05 0.07060,
# -0.1 0.07813, -0.15 ~0.0848, -0.2 0.09116).
export CUDA_VISIBLE_DEVICES=-1
while powershell -NoProfile -Command "(Get-CimInstance Win32_Process -Filter \"name='python.exe'\" | Where-Object { \$_.CommandLine -like '*cert_adjoint*' }).Count" | grep -q '^[1-9]'; do sleep 10; done
timeout 1750 py -u cert_adjoint.py window -0.22 > run_w-0.22.log 2>&1
for a in "0.05 0.0725" "0.1 0.0815" "0.15 0.0902" "0.2 0.0986" "-0.05 0.0721" "-0.1 0.0797" "-0.15 0.0866" "-0.2 0.0930"; do
  set -- $a
  timeout 1750 py -u cert_adjoint.py sup $1 $2 > run_s$1.log 2>&1
done
echo queue-done
