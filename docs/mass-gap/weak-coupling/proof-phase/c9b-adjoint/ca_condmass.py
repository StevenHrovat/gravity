"""C-A (PREREG-PILOT2.md, addition for ROUTE3.md): condition A's conditional mass from the W2 snapshots (read only).
Conditional connected correlator of fine plaquettes q0 = (1/2) tr U_p, given one instance (one frozen outside, one sampled block field),
over the 16 independent chain-A boxes of that instance; pairs of parallel plaquettes separated by r along a direction perpendicular to
their plane (no shared links); averaged over positions, orientations and instances; jackknife over chains.
    py ca_condmass.py            (run from this folder; imports W2's code from ../c9a-crossover/w2)"""
import json
import math
import os
import sys
from collections import defaultdict

import numpy as np

W2 = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "c9a-crossover", "w2")
sys.path.insert(0, W2)
os.chdir(W2)
import constrained as C  # noqa: E402
from lever_proxy import launch_snapshots, prod_seq  # noqa: E402


def main(tag="snap_end"):
    geo = C.Geometry(6)
    F, off, ell = geo.F, geo.off, geo.ell
    base = geo.plaq[:, 0] // 4
    coords = np.stack(np.unravel_index(base, (F,) * 4), axis=-1) - off
    mu = geo.plaq[:, 0] % 4
    nu = geo.plaq[:, 3] % 4 if geo.plaq.shape[1] > 3 else None
    # plane of each plaquette: the two directions among its links
    planes = []
    for row in geo.plaq:
        ds = sorted(set(int(l % 4) for l in row if l < geo.NL))
        planes.append(tuple(ds[:2]))
    idx = {(tuple(c), pl): i for i, (c, pl) in enumerate(zip(coords.tolist(), planes))}
    pairs = {r: [] for r in (1, 2, 3)}
    for i, (c, pl) in enumerate(zip(coords.tolist(), planes)):
        if not all(0 <= v < ell - 1 for v in c):  # keep plaquettes well inside the box
            continue
        for rho in range(4):
            if rho in pl:
                continue
            for r in (1, 2, 3):
                c2 = list(c)
                c2[rho] += r
                j = idx.get((tuple(c2), pl))
                if j is not None and all(0 <= v < ell - 1 for v in c2):
                    pairs[r].append((i, j))
    inside = [i for i, c in enumerate(coords.tolist()) if all(0 <= v < ell - 1 for v in c)]
    out = {"pairs_per_r": {r: len(v) for r, v in pairs.items()}, "n_plaq_inside": len(inside), "beta": {}}
    for beta in (2.3, 3.5):
        groups = defaultdict(list)  # (launch, instance) -> list of q0 arrays (one per chain)
        for s in (101, 102, 103):
            js = f"runs/narrow/launch_b{beta}_s{s}.json"
            if not os.path.exists(js):
                continue
            for (tg, b, ycl, pool, j, p, U, Y) in launch_snapshots(js):
                if tg != tag or ycl != "sampled":
                    continue
                groups[(s, j)].append(prod_seq(U, geo.plaq, geo.plaqd)[..., 0])
        G = [np.array(v) for v in groups.values() if len(v) >= 4]
        nch = min(len(g) for g in G)
        G = [g[:nch] for g in G]

        def corr(drop=None):
            res = {}
            for r in (0, 1, 2, 3):
                vals = []
                for g in G:
                    x = g if drop is None else np.delete(g, drop, axis=0)
                    xc = x - x.mean(axis=0)
                    if r == 0:
                        vals.append(float((xc[:, inside] ** 2).mean()))
                    else:
                        a = np.array(pairs[r])
                        vals.append(float((xc[:, a[:, 0]] * xc[:, a[:, 1]]).mean()))
                res[r] = float(np.mean(vals)) * nch / (nch - 1 if drop is None else nch - 2)
            return res
        full = corr()
        jk = [corr(k) for k in range(nch)]
        sd = {r: float(math.sqrt((nch - 1) / nch * sum((j[r] - np.mean([q[r] for q in jk])) ** 2 for j in jk))) for r in full}
        row = {"instances": len(G), "chains_per_instance": nch, "C": full, "sd": sd,
               "ratio_C1_C0": full[1] / full[0]}
        if full[2] > 2 * sd[2] and full[1] > 0:
            row["m_f"] = math.log(full[1] / full[2])
            row["m_f_kind"] = "resolved: log(C1/C2)"
        elif full[1] > 2 * sd[1]:
            row["m_f_lower"] = math.log(full[1] / (2 * sd[2]))
            row["m_f_kind"] = "C2 not resolved: lower bound log(C1/(2 sd C2))"
        else:
            row["m_f_kind"] = "C1 not resolved"
        m = row.get("m_f", row.get("m_f_lower"))
        if m is not None:
            row["m_Lblock_b2"] = 2 * m
        out["beta"][str(beta)] = row
        print(json.dumps({str(beta): row}), flush=True)
    return out


if __name__ == "__main__":
    o = main(sys.argv[1] if len(sys.argv) > 1 else "snap_end")
    here = os.path.dirname(os.path.abspath(__file__))
    json.dump(o, open(os.path.join(here, "..", "c9b-adjoint", "ca_condmass.json") if False else os.path.join(here, "ca_condmass.json"), "w"), indent=1)
