"""Generate SU(2) configurations and measure: the plaquette, torelon correlators (string tension, Teper's method) and scalar glueball
correlators (the mass gap channel, 0++). Writes one .npz of raw per-measurement data; analyse.py turns it into numbers with errors.

Usage: python3 run_su2.py BETA L T N_THERM N_MEAS SEED OUT.npz [N_OR] [EVERY]
"""

import sys
import time

import numpy as np

from su2 import Lattice, qmul, shift


def torelon_ops(lat, V):
    """Per time slice: the zero-momentum sum of the spatial Polyakov loops (flux closed around the periodic spatial box) in the three
    spatial directions, from the smeared links."""
    T, L = lat.shape[0], lat.shape[1]
    out = np.zeros(T)
    for i in (1, 2, 3):
        loop = lat.line(V, i, L)
        out += loop[..., 0].sum(axis=(1, 2, 3)) / L  # each loop counted once per site along it
    return out


def main():
    beta, L, T = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    n_therm, n_meas, seed, out = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), sys.argv[7]
    n_or = int(sys.argv[8]) if len(sys.argv) > 8 else 4
    every = int(sys.argv[9]) if len(sys.argv) > 9 else 2
    lat = Lattice(T, L, beta, seed)
    t0 = time.time()
    for s in range(n_therm):
        lat.heatbath()
        for _ in range(n_or):
            lat.overrelax()
        if s % 10 == 0:
            lat.reunitarise()
    plaq, glue, tor = [], [], []
    smear_levels = (4, 12)  # APE steps with alpha = 0.5
    for m in range(n_meas):
        for _ in range(every):
            lat.heatbath()
            for _ in range(n_or):
                lat.overrelax()
        lat.reunitarise()
        plaq.append(lat.plaquette())
        g, tr = [], []
        V = lat.U
        done = 0
        for n in smear_levels:
            V = lat_smear_more(lat, V, n - done)
            done = n
            g.append(lat.glueball_ops(V))
            tr.append(torelon_ops(lat, V))
        glue.append(np.concatenate(g, axis=0))
        tor.append(np.array(tr))
        if m % 50 == 0:
            print(f"beta={beta} L={L} meas {m}/{n_meas} plaq={np.mean(plaq):.5f} t={time.time() - t0:.0f}s", flush=True)
    np.savez(out, beta=beta, L=L, T=T, seed=seed, n_therm=n_therm, n_or=n_or, every=every, smear_levels=np.array(smear_levels),
             plaq=np.array(plaq), glue=np.array(glue), tor=np.array(tor), seconds=time.time() - t0)
    print(f"done {out} plaq={np.mean(plaq):.5f} in {time.time() - t0:.0f}s", flush=True)


def lat_smear_more(lat, V, n, alpha=0.5):
    """APE-smear the spatial links of V by n more steps."""
    saved = lat.U
    lat.U = V
    W = lat.ape_smear_spatial(alpha=alpha, n=n)
    lat.U = saved
    return W


if __name__ == "__main__":
    main()
