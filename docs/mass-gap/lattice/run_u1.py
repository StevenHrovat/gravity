"""Generate U(1) configurations and record the photon operators. Usage:
python3 run_u1.py BETA L T N_THERM N_MEAS SEED OUT.npz [N_OR] [EVERY]
"""

import sys
import time

import numpy as np

from u1 import U1Lattice


def main():
    beta, L, T = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    n_therm, n_meas, seed, out = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), sys.argv[7]
    n_or = int(sys.argv[8]) if len(sys.argv) > 8 else 3
    every = int(sys.argv[9]) if len(sys.argv) > 9 else 2
    lat = U1Lattice(T, L, beta, seed)
    t0 = time.time()
    for _ in range(n_therm):
        lat.heatbath()
        for _ in range(n_or):
            lat.overrelax()
    plaq, ops = [], []
    for m in range(n_meas):
        for _ in range(every):
            lat.heatbath()
            for _ in range(n_or):
                lat.overrelax()
        plaq.append(lat.plaquette())
        ops.append(lat.photon_ops())
        if m % 100 == 0:
            print(f"U(1) beta={beta} L={L} meas {m}/{n_meas} plaq={np.mean(plaq):.5f} t={time.time() - t0:.0f}s", flush=True)
    np.savez(out, beta=beta, L=L, T=T, seed=seed, n_therm=n_therm, n_or=n_or, every=every, plaq=np.array(plaq), ops=np.array(ops),
             seconds=time.time() - t0)
    print(f"done {out} plaq={np.mean(plaq):.5f} in {time.time() - t0:.0f}s", flush=True)


if __name__ == "__main__":
    main()
