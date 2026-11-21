"""Check the loop equations of su2boot.py against Monte Carlo configurations (residual = sum coeff * w must vanish within errors).

Usage (from docs/mass-gap/): py bootstrap/check_equations.py [d] [L] [beta] [n_meas] [Wmax]
Writes results/bootstrap_eqcheck_d{d}.json.
"""

import os
os.environ['CUDA_VISIBLE_DEVICES'] = '-1'  # never touch the GPU (it runs other jobs); set before any other import


import json
import os
import random
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(__file__))
import su2boot as sb
from mc_reference import LatticeD


def main():
    d = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    L = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    beta = float(sys.argv[3]) if len(sys.argv) > 3 else 2.0
    n_meas = int(sys.argv[4]) if len(sys.argv) > 4 else 400
    Wmax = int(sys.argv[5]) if len(sys.argv) > 5 else 6
    eqs = sb.all_loop_equations(d, Wmax + 4, Wmax)
    rnd = random.Random(3)
    if len(eqs) > 60:
        eqs = rnd.sample(eqs, 60)
    keys = sorted({k for e in eqs for k in e if k != ()}, key=lambda k: (len(k), k))
    print(f'd={d}: {len(eqs)} equations, {len(keys)} loops', flush=True)
    lat = LatticeD(d, L, beta, 7)
    for i in range(200):
        lat.heatbath()
        lat.overrelax()
    vals = np.zeros((n_meas, len(keys)))
    t0 = time.time()
    for m in range(n_meas):
        lat.heatbath()
        lat.overrelax()
        lat.overrelax()
        lat.reunitarise()
        for j, k in enumerate(keys):
            vals[m, j] = lat.loop(sb.key_to_path(k))
    idx = {k: j for j, k in enumerate(keys)}
    out = []
    worst = 0.0
    for e in eqs:
        r = np.zeros(n_meas)
        scale = 0.0
        for k, (c0, c1) in e.items():
            c = float(c0) + float(c1) * beta
            v = 1.0 if k == () else vals[:, idx[k]]
            r = r + c * v
            scale += abs(c)
        nb = 20
        n = n_meas // nb * nb
        b = r[:n].reshape(nb, -1).mean(1)
        mean, err = float(r.mean()), float(b.std(ddof=1) / np.sqrt(nb))
        z = mean / err if err > 0 else 0.0
        worst = max(worst, abs(z))
        out.append(dict(n_terms=len(e), residual=mean, error=err, z=z, scale=scale))
    zs = np.array([o['z'] for o in out])
    print(f'd={d} beta={beta} L={L}: {len(out)} equations, |z| max {np.abs(zs).max():.2f}, rms z {np.sqrt((zs**2).mean()):.2f}, '
          f'median |residual|/scale {np.median([abs(o["residual"])/o["scale"] for o in out]):.2e}, {time.time()-t0:.0f}s')
    path = os.path.join(os.path.dirname(__file__), '..', 'results', f'bootstrap_eqcheck_d{d}.json')
    with open(path, 'w') as f:
        json.dump(dict(d=d, L=L, beta=beta, n_meas=n_meas, Wmax=Wmax, z_max=float(np.abs(zs).max()),
                       z_rms=float(np.sqrt((zs ** 2).mean())), equations=out), f, indent=1)


if __name__ == '__main__':
    main()
