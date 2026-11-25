"""Exact single-link Dobrushin influence for 4D Wilson lattice gauge theory, SU(2) and U(1) (floating point, not rigorous).

A link's conditional law has density exp(beta <x, A>) on S^3 (SU(2) as unit quaternions) or S^1 (U(1)), A = sum of 6 staples. Changing
one neighbouring link swaps one staple v -> v'. C(beta) = sup TV over the other staples' sum W (|W| <= 5) and unit v, v'; alpha = 18 C.

Reduction: write v = s + d, v' = s - d (s perpendicular to d, |s|^2 + |d|^2 = 1), m = W + s. Then the two laws have mean parameters
beta (m + d), beta (m - d); with d = delta e1 the constraint |W| <= 5 reads m1^2 + (|m2| - sqrt(1 - delta^2))^2 <= 25. The laws depend
on x only through its projection to the plane of the two parameters; for uniform S^3 that projection is uniform on the unit disk.

Usage: python single_link.py  (prints a table and writes single_link.json next to this file)
"""

import json
import os
import sys

import numpy as np
from scipy import optimize, special

NEIGHBOURS = 18  # 6 (d - 1) for d = 4
WMAX = 5.0       # 2 (d - 1) - 1 other staples

# Quadrature: unit disk (SU(2)) in polar Gauss-Legendre, circle (U(1)) uniform.
_r, _wr = np.polynomial.legendre.leggauss(160)
_r = 0.5 * (_r + 1); _wr = 0.5 * _wr
_th = np.linspace(0, 2 * np.pi, 720, endpoint=False)
_R, _T = np.meshgrid(_r, _th, indexing="ij")
DISK_Y1, DISK_Y2 = _R * np.cos(_T), _R * np.sin(_T)
DISK_W = (_wr[:, None] * _R) * (2 * np.pi / len(_th)) / np.pi   # integrates to 1 (uniform on the disk)
CIRC_Y1, CIRC_Y2 = np.cos(_th), np.sin(_th)
CIRC_W = np.full(_th.shape, 1.0 / len(_th))


def logZ(group, r):
    if group == "SU(2)":
        return np.log(2.0) + np.log(special.ive(1, r)) + r - np.log(r) if r > 1e-12 else 0.0
    return np.log(special.ive(0, r)) + r


def tv(group, a, b):
    """TV distance between exp(<y,a>)/Z and exp(<y,b>)/Z, a and b given in the plane (2-vectors)."""
    y1, y2, w = (DISK_Y1, DISK_Y2, DISK_W) if group == "SU(2)" else (CIRC_Y1, CIRC_Y2, CIRC_W)
    fa = np.exp(a[0] * y1 + a[1] * y2 - logZ(group, np.hypot(*a)))
    fb = np.exp(b[0] * y1 + b[1] * y2 - logZ(group, np.hypot(*b)))
    return 0.5 * np.sum(w * np.abs(fa - fb))


def influence(group, beta, p):
    """p = (delta, m1, m2), projected onto the feasible set; returns TV."""
    delta = np.clip(p[0], 0.0, 1.0)
    s = np.sqrt(max(0.0, 1 - delta ** 2))
    m1, m2 = p[1], p[2]
    dist = np.hypot(m1, abs(m2) - s)
    if dist > WMAX:  # pull back onto the boundary of the feasible set
        t = WMAX / dist
        m1, m2 = m1 * t, np.sign(m2 or 1.0) * (s + (abs(m2) - s) * t)
    a = beta * np.array([m1 + delta, m2])
    b = beta * np.array([m1 - delta, m2])
    return tv(group, a, b)


def sup_influence(group, beta):
    best, arg = -1.0, None
    for delta in (0.25, 0.5, 0.75, 1.0):
        for m1 in np.linspace(-6, 6, 13):
            for m2 in np.linspace(0, 6, 7):
                v = influence(group, beta, (delta, m1, m2))
                if v > best:
                    best, arg = v, (delta, m1, m2)
    res = optimize.minimize(lambda p: -influence(group, beta, p), arg, method="Nelder-Mead",
                            options={"xatol": 1e-6, "fatol": 1e-10, "maxiter": 4000})
    if -res.fun > best:
        best, arg = -res.fun, tuple(res.x)
    return best, arg


def mc_check(beta, n=400000, seed=1):
    """Direct Monte Carlo on S^3 for one configuration (delta = 1, m = 0): checks the disk-projection shortcut."""
    rng = np.random.default_rng(seed)
    x = rng.normal(size=(n, 4)); x /= np.linalg.norm(x, axis=1, keepdims=True)
    a, b = beta * np.array([1.0, 0, 0, 0]), beta * np.array([-1.0, 0, 0, 0])
    lz = logZ("SU(2)", beta)
    d = np.abs(np.exp(x @ a - lz) - np.exp(x @ b - lz))
    return 0.5 * d.mean(), 0.5 * d.std() / np.sqrt(n)


def main():
    out = {"neighbours": NEIGHBOURS, "groups": {}}
    lin = {"SU(2)": 4 / (3 * np.pi), "U(1)": 2 / np.pi}
    b0 = 1e-3
    for g in ("SU(2)", "U(1)"):
        c0, _ = sup_influence(g, b0)
        print(f"{g}: C({b0}) = {c0:.6e}, linearisation {lin[g] * b0:.6e}, ratio {c0 / (lin[g] * b0):.4f}")
        rows = []
        for beta in (0.02, 0.05, 0.08, 0.1, 0.12, 0.15, 0.2, 0.3, 0.5, 1.0, 2.0):
            c, arg = sup_influence(g, beta)
            rows.append({"beta": beta, "C": c, "alpha": NEIGHBOURS * c, "argmax": [float(x) for x in arg]})
            print(f"  beta={beta:5.2f}  C={c:.5f}  alpha={NEIGHBOURS * c:.4f}  at (delta, m1, m2)={tuple(round(float(x), 3) for x in arg)}")
        star = optimize.brentq(lambda bb: NEIGHBOURS * sup_influence(g, bb)[0] - 1.0, 0.01, 0.3, xtol=1e-5)
        print(f"  beta* = {star:.5f}")
        out["groups"][g] = {"C_small_beta": c0, "linearisation": lin[g] * b0, "rows": rows, "beta_star": star}
    mc, mce = mc_check(0.1)
    sh = influence("SU(2)", 0.1, (1.0, 0.0, 0.0))
    print(f"MC check on S^3 at beta=0.1, delta=1, m=0: MC {mc:.5f} +- {mce:.5f}, disk shortcut {sh:.5f}")
    out["mc_check"] = {"beta": 0.1, "mc": mc, "mc_err": mce, "disk": sh}
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "single_link.json"), "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    sys.exit(main())
