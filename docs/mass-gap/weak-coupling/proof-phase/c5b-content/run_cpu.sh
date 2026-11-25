#!/bin/bash
# the three pre-registered CPU runs, one process at a time (PREREG.md section 3)
cd "$(dirname "$0")"
export CUDA_VISIBLE_DEVICES=-1
python content.py run su2 2.3 16 2301 110 40 80 3 80 1500 runs-cpu/su2_b2.3_N16.json > runs-cpu/su2_b2.3_N16.out 2>&1
python content.py run su2 2.5 16 2501 110 40 80 3 80 1500 runs-cpu/su2_b2.5_N16.json > runs-cpu/su2_b2.5_N16.out 2>&1
python content.py run u1 1.1 16 1101 110 40 80 3 80 1500 runs-cpu/u1_b1.1_N16.json > runs-cpu/u1_b1.1_N16.out 2>&1
