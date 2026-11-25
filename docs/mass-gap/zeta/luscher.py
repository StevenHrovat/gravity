"""Fit the closed flux tube's energy E(L) = sigma L - c/L and compare c with pi/3 = -4 pi zeta(-1) (PREREG-LUSCHER.md).

Usage: python luscher.py RUN_L6.npz RUN_L8.npz ...   (the torelon runs; analysed with ../lattice/analyse_plateau.py)
"""

import json
import math
import os
import sys

import numpy as np
from scipy import optimize, stats

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lattice"))
from analyse_plateau import analyse  # noqa: E402


def fit(Ls, E, dE, nambu_goto=False):
    Ls, E, dE = map(np.asarray, (Ls, E, dE))
    if nambu_goto:
        f = lambda L, s: s * L * np.sqrt(np.clip(1 - 2 * np.pi / (3 * s * L * L), 1e-12, None))
        p, cov = optimize.curve_fit(f, Ls, E, p0=[0.13], sigma=dE, absolute_sigma=True)
    else:
        f = lambda L, s, c: s * L - c / L
        p, cov = optimize.curve_fit(f, Ls, E, p0=[0.13, 1.0], sigma=dE, absolute_sigma=True)
    chi2 = float(np.sum(((f(Ls, *p) - E) / dE) ** 2))
    dof = len(Ls) - len(p)
    return p, np.sqrt(np.diag(cov)), chi2, dof, (float(stats.chi2.sf(chi2, dof)) if dof > 0 else float("nan"))


def main(paths):
    rows = []
    for p in paths:
        r = analyse(p)
        if "torelon_mass" in r:
            rows.append((r["L"], *r["torelon_mass"], r["t_torelon"]))
            print(f"L={r['L']:2d}: torelon E = {r['torelon_mass'][0]:.4f} +- {r['torelon_mass'][1]:.4f} (plateau at t={r['t_torelon']})")
        else:
            print(f"L={r['L']:2d}: no plateau")
    rows.sort()
    out = {"points": rows}
    for name, sel in (("all", rows), ("L>=8", [x for x in rows if x[0] >= 8])):
        if len(sel) < 3:
            continue
        Ls, E, dE = [x[0] for x in sel], [x[1] for x in sel], [x[2] for x in sel]
        (s, c), (ds, dc), chi2, dof, pv = fit(Ls, E, dE)
        dev = (c - math.pi / 3) / dc
        verdict = "pass" if abs(dev) <= 2 and pv > 0.05 else ("tension" if abs(dev) <= 3 else "fail")
        print(f"[{name}] sigma = {s:.4f} +- {ds:.4f} (a sqrt(sigma) = {math.sqrt(s):.4f}), c = {c:.3f} +- {dc:.3f} "
              f"(pi/3 = 1.047, {dev:+.1f} errors); zeta(-1) measured = {-c / (4 * math.pi):.4f} +- {dc / (4 * math.pi):.4f}; "
              f"chi2/dof = {chi2:.1f}/{dof}, p = {pv:.2f}: {verdict}")
        (sng,), (dsng,), chi2n, dofn, pvn = fit(Ls, E, dE, nambu_goto=True)
        print(f"   Nambu-Goto, sigma only: sigma = {sng:.4f} +- {dsng:.4f}, chi2/dof = {chi2n:.1f}/{dofn}, p = {pvn:.2f}")
        out[name] = {"sigma": [s, ds], "c": [c, dc], "zeta_m1": [-c / (4 * math.pi), dc / (4 * math.pi)], "chi2": chi2, "dof": dof,
                     "p": pv, "verdict": verdict, "nambu_goto_sigma": [sng, dsng], "nambu_goto_chi2": chi2n, "nambu_goto_p": pvn}
    print(json.dumps(out))


if __name__ == "__main__":
    main(sys.argv[1:])
