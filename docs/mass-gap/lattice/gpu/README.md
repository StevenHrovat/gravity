# The GPU path for the SU(2) lattice (2026-11-21)

`run_su2_gpu.py` (one folder up) does what `run_su2.py` does, on an NVIDIA GPU: same update, same measurements, same output file, so
`analyse.py` reads it unchanged. The update and the APE smearing run in fused CUDA kernels taken from the GUID v7 lattice code.

## Provenance

`su3_cuda.py` and `gauge.py` are copied **unchanged** from the GUID v7 lattice code (the first author's laptop, folder `qcd/`, no
repository; the code behind GUID v7's SU(3) results). Pure-gauge SU(N) for N = 2 or 3: Kennedy–Pendleton heat bath (Cabibbo–Marinari
subgroups for SU(3)) and overrelaxation on a checkerboard per link direction, reunitarisation, plaquette, Polyakov loop, APE smearing,
straight lines and Wilson loops; B independent lattices are updated in one launch.

| file | sha256 |
|---|---|
| `gauge.py` | `ecc449483a53f35fb5faf8cdec95a015f589a5aff2e4568ce7ba86335cf8ec7a` |
| `su3_cuda.py` | `25b3dcf7c51446649c6482ce00041922b79b3bd1560afdc2a63f216307c0d17b` |

## Checks

- **Same measurements:** `python run_su2_gpu.py selftest` builds a configuration on the GPU, converts it to `su2.py`'s quaternion layout
  and compares every measurement (plaquette, the 1×1 and 2×2 glueball operators and the torelons at both smearing levels, so the
  smearing too): largest difference 2.8 × 10⁻¹⁴.
- **Same physics:** β = 2.3 on 10⁴, 3000 measurements, the settings of the CPU run: plaquette 0.60228 ± 0.00005 (CPU 0.60224 ± 0.00006);
  a√σ = 0.384 ± 0.011 (CPU 0.363 ± 0.011, Teper 0.3687 ± 0.0022); a·m₀₊₊ = 1.19 ± 0.08 (CPU 1.24 ± 0.05, Teper 1.216 ± 0.023).
  Independent chains, agreement within errors.

## Speed (`python gpu/bench.py`, RTX 3080 laptop GPU against one laptop CPU core)

One measurement = two update sweeps (1 heat bath + 3 overrelaxation each) + the measurement.

| lattice | CPU, numpy, one core | GPU, 10 chains, per chain | factor |
|---|---|---|---|
| 10⁴ | about 0.75 s | 7.4 ms | about 100 |
| 14⁴ | about 3.7 s | 29 ms | about 125 |
| 20⁴ | about 15 s (estimated from 14⁴) | 124 ms | about 120 |

The CPU numbers were taken while other runs shared the machine; take them as approximate. Against all spare CPU cores together the GPU is
still about five to six times faster, and it leaves the cores free. The measurement code multiplies the 2 × 2 matrices elementwise:
`cp.matmul` on millions of tiny matrices was seventeen times slower.

## Setup

```sh
python -m pip install --user "cupy-cuda12x[ctk]==14.2.0"     # brings NVIDIA's CUDA libraries as pip packages; no system CUDA needed
python run_su2_gpu.py selftest                               # must print OK
python run_su2_gpu.py 2.4 14 14 300 2000 24 su2_b2.4_L14_gpu.npz 3 2 10   # 10 chains of 2000 measurements
```
