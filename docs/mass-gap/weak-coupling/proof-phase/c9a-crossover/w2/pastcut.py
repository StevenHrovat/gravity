"""Past-cut plaquette fractions (q0 = (1/2) tr U_p < 0, i.e. centre layer tau_p = -1 in M1's split) at block factors 1, 2, 4 of the
saved 16^4 equilibrium configurations, both beta (CPU; RATE.md). Also the largest past-cut cluster share and spanning (cube
adjacency, as coarse_test.py). Reuses coarse_test.py's blocking.

Usage: py pastcut.py [--out runs/pastcut.json]
"""
import argparse
import itertools
import json

import numpy as np

import coarse_test as T


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="runs/pastcut.json")
    a = ap.parse_args()
    out = {}
    for beta in (2.3, 3.5):
        confs = np.load(f"runs/conf_b{beta}.npz")["U"]
        res = {}
        for fac in (1, 2, 4):
            fr, lf, sp = [], [], []
            offs = [(0, 0, 0, 0)] if fac == 1 else list(itertools.product((0, fac // 2), repeat=4))
            for ci in range(confs.shape[0]):
                for o in offs:
                    U = confs[ci]
                    for mu in range(4):
                        U = np.roll(U, -o[mu], axis=1 + mu)
                    for _ in range({1: 0, 2: 1, 4: 2}[fac]):
                        U = T.block(U)
                    q = T.plaquettes(U)
                    past = q < 0
                    sizes, span, mx = T.clusters(past)
                    fr.append(float(past.mean()))
                    lf.append(mx / past.size)
                    sp.append(span)
            res[str(fac)] = dict(frac_past_cut=float(np.mean(fr)), largest_share=float(np.mean(lf)),
                                 spanning_frac=float(np.mean(sp)), n=len(fr))
            print(beta, fac, res[str(fac)], flush=True)
        out[str(beta)] = res
    json.dump(out, open(a.out, "w"), indent=1)


if __name__ == "__main__":
    main()
