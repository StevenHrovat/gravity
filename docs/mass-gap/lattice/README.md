# Lattice gauge theory in four dimensions: SU(2) and U(1)

Small, readable numpy code for the two theories the mass-gap explainer ([`../README.md`](../README.md)) compares: SU(2), a two-colour
cousin of the strong force with a mass gap (expected, not proved), and U(1), the lattice theory of light, with a massless photon at weak
coupling (proved). Everything reproduces published numbers; nothing here proves anything. It stands in for the GUID v7 lattice code,
which is kept on the first author's laptop and is in no repository.

| File | What it does |
|---|---|
| `su2.py` | SU(2) links as unit quaternions; Wilson action; Kennedy–Pendleton heat bath and overrelaxation on a checkerboard; APE smearing; Wilson loops, torelons, glueball operators |
| `run_su2.py` | generates configurations and records the plaquette, torelon (flux around the box) and scalar glueball (0⁺⁺) operators |
| `u1.py`, `run_u1.py` | compact U(1): exact heat bath (von Mises) and overrelaxation; the photon operator (a transverse magnetic field at the smallest momenta) |
| `analyse.py` | variational correlator analysis with jackknife errors: the glueball mass, the string tension from torelons (Teper's method), the photon energy against the free massless dispersion |

Every random number comes from one seeded generator, so a run is reproducible on one platform. Checks done before the production runs:
the quaternion product equals the 2 × 2 matrix product; the SU(2) plaquette at β = 2.5 on 8⁴ is 0.6526 (the commonly quoted value is
0.652) and at β = 2.3 it is 0.6025 (0.602); in U(1) at β = 1.2 the photon's energy at the two smallest momenta on 8³ × 16 is 0.70(3) and
1.33(9), against 0.75 and 1.32 for a massless particle.

## Reproduce

Needs Python 3 with numpy. From this folder:

```sh
python3 run_su2.py 2.3 10 10 300 3000 23 su2_b2.3_L10.npz 3 2
python3 run_su2.py 2.4 14 14 300 2000 24 su2_b2.4_L14.npz 3 2
python3 run_su2.py 2.5 16 16 300 1500 25 su2_b2.5_L16.npz 3 2
python3 run_u1.py 1.2 8 16 300 1500 31 u1_b1.2_L8.npz 3 2
python3 run_u1.py 1.2 12 24 300 1200 32 u1_b1.2_L12.npz 3 2
python3 run_u1.py 0.8 8 16 300 1500 33 u1_b0.8_L8.npz 3 2
python3 run_u1.py 0.8 12 24 300 1200 34 u1_b0.8_L12.npz 3 2
python3 analyse.py *.npz > summary.json
```

Arguments: β, spatial size L, time size T, thermalisation sweeps, measurements, seed, output file, overrelaxation steps per heat bath,
sweeps between measurements. On a 4-core cloud box the SU(2) runs take 0.5, 2 and 3 hours (one core each).

## Longer runs on a laptop (optional)

Two finer grids would add points to the "gap in grid units shrinks, in real units stays" table (Teper's values: β = 2.6, a√σ = 0.1326(30),
am₀₊₊ = 0.51(3); β = 2.7, 0.1005(20), 0.39(3)). Each needs about 5 to 15 hours on one core. In WSL (Ubuntu), in a checkout of this branch:

**laptop · WSL (Ubuntu) · your own user**

```sh
cd ~/gravity/docs/mass-gap/lattice && python3 -m pip install --user numpy
nohup python3 run_su2.py 2.6 20 20 300 1000 26 su2_b2.6_L20.npz 3 2 > su2_b2.6.log 2>&1 &
```

Then commit `su2_b2.6_L20.npz` to `docs/mass-gap/results/` on the branch (or attach it to the pull request), and the next session analyses
it. The GUID v7 GPU code, if it is put in a repository, does the same far faster.
