#!/bin/bash
# c6d runs (PREREG-AMEND.md sections 3 and 4): photon first; the SU(2) runs only if the photon gate holds. One process at a time.
# usage: run_cpu.sh photon | su2_2.3 | su2_2.5   (each at most 30 minutes)
cd "$(dirname "$0")"
export CUDA_VISIBLE_DEVICES=-1 OMP_NUM_THREADS=8 OPENBLAS_NUM_THREADS=8 MKL_NUM_THREADS=8
case "$1" in
  photon)   timeout 1800 python content.py run u1 1.1 16 1101 110 40 80 3 80 1500 runs-cpu/u1_b1.1_N16.json > runs-cpu/u1_b1.1_N16.out 2>&1 ;;
  su2_2.3)  timeout 1800 python content.py run su2 2.3 16 2301 110 40 80 3 80 1500 runs-cpu/su2_b2.3_N16.json > runs-cpu/su2_b2.3_N16.out 2>&1 ;;
  su2_2.5)  timeout 1800 python content.py run su2 2.5 16 2501 110 40 80 3 80 1500 runs-cpu/su2_b2.5_N16.json > runs-cpu/su2_b2.5_N16.out 2>&1 ;;
esac
