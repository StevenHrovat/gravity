"""PREREG run 2, design addendum (float only): how much does B1 lose by relaxing M over all traceless matrices?
The moved staple a is one of the six staples, so S - a a^T is PSD (S = sum_k a_k a_k^T, eigenvalues s): sum_i a_i^2 / s_i <= 1
in the eigenbasis. Here: B1 with M = sym(a b^T) restricted to such a (b unit, b perp a), maximised numerically (random starts),
against the relaxed B1, at the worst simplex points of explore.py and a few others."""
import os

os.environ.setdefault("CUDA_VISIBLE_DEVICES", "-1")
import numpy as np
from scipy.optimize import minimize

import bingham as bg


def forms(lam):
    """the quadratic form of B1 (per unit ||M||_F^2): pair coefficients P (4x4) and the diagonal 4x4 form Qd"""
    Z, m1, m2 = bg.moments_float(lam[None])
    Z2, n1, n2 = bg.moments_float(2 * lam[None])
    zeta = (Z2 / Z ** 2)[0]
    m1, m2, n1, n2 = m1[0], m2[0], n1[0], n2[0]
    C = m2 - np.outer(m1, m1)
    dm = n1 - m1
    C2 = n2 - np.outer(n1, n1) + np.outer(dm, dm)
    P = np.zeros((4, 4))
    for i in range(4):
        for j in range(4):
            if i != j:
                w = 24 * m2[i, j]
                P[i, j] = (w - 1) ** 2 / 96 + (2 * zeta * n2[i, j] - w ** 2 / 12) / 24
    Pr = np.eye(4) - 1 / 4
    E = 12 * Pr @ C @ Pr - Pr
    Qd = E @ E / 96 + Pr @ (zeta * C2 - 12 * C @ Pr @ C) @ Pr / 24
    return P, Qd


def qval(M, P, Qd):
    d = np.diag(M)
    off = sum(P[i, j] * 2 * M[i, j] ** 2 for i in range(4) for j in range(i + 1, 4))
    return off + d @ Qd @ d


def constrained(s, kappa, starts=60, seed=0):
    lam = kappa * s if kappa > 0 else -kappa * (6 - s)
    P, Qd = forms(lam)
    rng = np.random.default_rng(seed)
    best = 0.0
    sup = s > 1e-12

    def unpack(z):
        a = np.where(sup, z[:4], 0.0)
        na = np.linalg.norm(a)
        a = a / na
        b = z[4:] - (z[4:] @ a) * a
        b = b / np.linalg.norm(b)
        return a, b

    def obj(z):
        a, b = unpack(z)
        viol = max(0.0, np.sum(np.where(sup, a ** 2 / np.where(sup, s, 1), 0)) - 1)
        M = (np.outer(a, b) + np.outer(b, a)) / 2
        return -qval(M, P, Qd) + 10 * viol
    for _ in range(starts):
        z0 = rng.normal(size=8)
        r = minimize(obj, z0, method="Nelder-Mead", options=dict(maxiter=4000, xatol=1e-9, fatol=1e-12))
        a, b = unpack(r.x)
        if np.sum(np.where(sup, a ** 2 / np.where(sup, s, 1), 0)) <= 1 + 1e-6:
            best = max(best, -r.fun)
    # relaxed value for comparison
    relaxed = 0.5 * max(P[np.triu_indices(4, 1)].max(), np.linalg.eigvalsh(
        np.array([[1, -1, 0, 0], [1, 1, -2, 0], [1, 1, 1, -3]]) @ Qd @ np.array([[1, -1, 0, 0], [1, 1, -2, 0], [1, 1, 1, -3]]).T
        / np.array([2, 6, 12])[:, None] ** 0.5 / np.array([2, 6, 12])[None, :] ** 0.5)[-1])
    return 1 / 16 + np.sqrt(best), 1 / 16 + np.sqrt(max(relaxed, 0))


for bA in (0.2, 0.22, 0.25, -0.2, -0.25):
    k = 4 * bA / 3
    rows = []
    for s in ((6, 0, 0, 0), (3, 3, 0, 0), (2, 2, 2, 0), (1.5, 1.5, 1.5, 1.5), (4, 1, 1, 0), (5, 1, 0, 0), (3, 1, 1, 1),
              (2, 2, 1, 1)):
        s = np.array(s, dtype=float)
        c, r = constrained(s, k)
        rows.append((c, r, s))
    for c, r, s in rows:
        print(f"b_A {bA:+.2f} s = {s}: constrained B1 {c:.5f}, relaxed {r:.5f}, column constrained {48 * abs(bA) * c:.4f}",
              flush=True)
