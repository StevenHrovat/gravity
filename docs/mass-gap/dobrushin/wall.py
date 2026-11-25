"""Shot in the dark for the block (Dobrushin-Shlosman) route: how far into the lattice does a frozen boundary reach?

All links based on the time slice t = 0 are frozen, either cold (identity) or hot (Haar random, fixed seed); everything else is updated
by heat bath and overrelaxation. Measured per configuration: the mean spatial plaquette on each time slice. The difference cold - hot
at distance r from the wall is the wall's influence; its decay length is the effective blast radius at that beta. Not rigorous: one
pair of boundary conditions, not the supremum over all of them.

Usage: python wall.py GROUP BETA L T N_THERM N_MEAS SEED BC OUT.npz      (GROUP su2 or u1, BC cold or hot)
"""

import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lattice"))
from su2 import Lattice  # noqa: E402
from u1 import U1Lattice  # noqa: E402


def freeze_wall(lat, bc, rng):
    t = np.indices(lat.shape)[0]
    lat.parity = [m & (t != 0) for m in lat.parity]  # updates never touch links based at t = 0
    if bc == "hot":
        if isinstance(lat, Lattice):
            q = rng.normal(size=(4,) + lat.shape[1:] + (4,))
            lat.U[:, 0] = q / np.linalg.norm(q, axis=-1, keepdims=True)
        else:
            lat.th[:, 0] = rng.uniform(-np.pi, np.pi, size=(4,) + lat.shape[1:])


def profile(lat):
    """Mean spatial plaquette per time slice: 1/2 Re tr for SU(2), cos for U(1)."""
    out = 0.0
    for mu in (1, 2, 3):
        for nu in range(mu + 1, 4):
            if isinstance(lat, Lattice):
                p = lat.plaquette_field(mu, nu)[..., 0]
            else:
                p = np.cos(lat.plaq_angle(mu, nu))
            out = out + p.mean(axis=(1, 2, 3))
    return out / 3.0


def main():
    group, beta, L, T = sys.argv[1], float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    n_therm, n_meas, seed, bc, out = int(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7]), sys.argv[8], sys.argv[9]
    lat = Lattice(T, L, beta, seed) if group == "su2" else U1Lattice(T, L, beta, seed)
    freeze_wall(lat, bc, np.random.default_rng(1000 + seed))
    t0 = time.time()

    def sweep():
        lat.heatbath()
        for _ in range(3):
            lat.overrelax()
        if group == "su2":
            lat.reunitarise()

    for _ in range(n_therm):
        sweep()
    prof = []
    for m in range(n_meas):
        sweep()
        sweep()
        prof.append(profile(lat))
    np.savez(out, group=group, beta=beta, L=L, T=T, bc=bc, seed=seed, prof=np.array(prof), seconds=time.time() - t0)
    print(f"done {out} in {time.time() - t0:.0f}s", flush=True)


if __name__ == "__main__":
    main()
