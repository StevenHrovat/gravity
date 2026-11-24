"""Analyse wall.py runs: the wall's influence Delta(r) = cold - hot at distance r, and its decay length.

Usage: python analyse_wall.py runs/*.npz   (prints a table, writes wall_summary.json next to this file)
"""

import glob
import json
import os
import sys
from collections import defaultdict

import numpy as np


def binned(x, nb=20):
    n = len(x) // nb * nb
    b = x[:n].reshape(nb, -1, *x.shape[1:]).mean(axis=1)
    return b.mean(axis=0), b.std(axis=0, ddof=1) / np.sqrt(nb)


def main(paths):
    runs = defaultdict(dict)
    for p in paths:
        d = np.load(p)
        key = (str(d["group"]), float(d["beta"]), int(d["L"]))
        runs[key][str(d["bc"])] = d
    out = []
    for key in sorted(runs):
        if set(runs[key]) != {"cold", "hot"}:
            continue
        g, beta, L = key
        T = int(runs[key]["cold"]["T"])
        rs = np.arange(1, T // 2 + 1)
        prof = {}
        for bc in ("cold", "hot"):
            pr = runs[key][bc]["prof"]
            sym = 0.5 * (pr[:, rs] + pr[:, (T - rs) % T])
            prof[bc] = binned(sym)
        delta = prof["cold"][0] - prof["hot"][0]
        err = np.hypot(prof["cold"][1], prof["hot"][1])
        ok = delta > 3 * err
        # use the leading run of significant points
        k = 0
        while k < len(ok) and ok[k]:
            k += 1
        ell, ell_err = None, None
        if k >= 2:
            y = np.log(delta[:k])
            w = (delta[:k] / err[:k]) ** 2
            A = np.vstack([np.ones(k), rs[:k]]).T
            cov = np.linalg.inv(A.T @ (w[:, None] * A))
            coef = cov @ (A.T @ (w * y))
            slope, s_err = coef[1], np.sqrt(cov[1, 1])
            if slope < 0:
                ell, ell_err = float(-1 / slope), float(s_err / slope ** 2)
        row = {"group": g, "beta": beta, "L": L, "plaq_mid": float(prof["cold"][0][-1]),
               "delta": [float(x) for x in delta], "err": [float(x) for x in err], "n_significant": int(k),
               "decay_length": ell, "decay_length_err": ell_err}
        out.append(row)
        dl = f"{ell:.2f} +- {ell_err:.2f}" if ell is not None else "n/a"
        print(f"{g:4s} beta={beta:4.2f} L={L:2d}  decay length {dl:>14s} (from {k} pts)  "
              + " ".join(f"{x:.1e}" for x in delta[:6]))
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "wall_summary.json"), "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    args = [q for a in sys.argv[1:] for q in glob.glob(a)]
    main(args)
