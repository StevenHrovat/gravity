"""Near-cut statistics on the W2 snapshots (CPU; for DICHOTOMY.md section 8). For every saved chain-A snapshot of a sampled box
(equilibrium outside, sampled block field): the fine plaquettes of the box, q0 = (1/2) tr U_p; the fraction with |q0| < delta
(within delta of the SO(3) cut, where the centre-layer flip cost beta |tr U_p| = 2 beta |q0| is below 2 beta delta), and the
fraction of blocks (2^4 fine sites) containing at least one such plaquette. delta values include the Peierls thresholds
delta_P = log K' / (2 beta) for K' = 6 and K' = 54.

Usage: py nearcut.py runs/narrow/launch_b*.json [--out runs/narrow/nearcut.json]
"""
import argparse
import json
import math

import numpy as np

import constrained as C
from lever_proxy import launch_snapshots, prod_seq


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("launches", nargs="+")
    ap.add_argument("--out", default="runs/narrow/nearcut.json")
    a = ap.parse_args()
    geo = C.Geometry(6)
    base = geo.plaq[:, 0] // 4
    coords = np.stack(np.unravel_index(base, (geo.F,) * 4), axis=-1) - geo.off
    bidx = np.ravel_multi_index(tuple((coords // 2).T), (geo.ell // 2,) * 4)
    nblk = (geo.ell // 2) ** 4
    acc = {}
    for js in a.launches:
        for (tag, beta, ycl, pool, j, p, U, Y) in launch_snapshots(js):
            if ycl != "sampled":
                continue
            q0 = prod_seq(U, geo.plaq, geo.plaqd)[..., 0]
            dP = {6: math.log(6) / (2 * beta), 54: math.log(54) / (2 * beta)}
            deltas = sorted({0.05, 0.1, 0.2, 0.3, 0.5, round(dP[6], 3), round(dP[54], 3)})
            r = acc.setdefault(beta, dict(n=0, q0_mean=0.0, frac={d: 0.0 for d in deltas}, blk={d: 0.0 for d in deltas},
                                          dP=dP, past_cut=0.0))
            r["n"] += 1
            r["q0_mean"] += float(q0.mean())
            r["past_cut"] += float(np.mean(q0 < 0))
            for d in deltas:
                near = np.abs(q0) < d
                r["frac"][d] += float(near.mean())
                hit = np.zeros(nblk, bool)
                np.logical_or.at(hit, bidx, near)
                r["blk"][d] += float(hit.mean())
    out = {}
    for beta, r in acc.items():
        n = r["n"]
        out[str(beta)] = dict(snapshots=n, plaquette_q0_mean=r["q0_mean"] / n, frac_past_cut=r["past_cut"] / n,
                              delta_P={str(k): v for k, v in r["dP"].items()},
                              frac_plaquettes_near_cut={str(d): v / n for d, v in r["frac"].items()},
                              frac_blocks_with_near_cut={str(d): v / n for d, v in r["blk"].items()})
    json.dump(out, open(a.out, "w"), indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
