"""Estimate k_A = ||h2 Haar||_KR on S^3 by an exact transport LP on a discretisation of the quotient by the chi-rotation
(kA_bounds.py has the coordinates; the measure is chi-invariant, so W1 on S^3 equals W1 on the quotient with the distance
d = arccos(rho rho' cos(psi - psi') + sqrt(1 - rho^2) sqrt(1 - rho'^2))). Cells: q = rho^2 uniform bins x psi bins, mass
of each cell at its centre (exact cell integrals of h2 Haar). An estimate, not a bound (discretisation error ~ cell size)."""
import math
import sys
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix


def kA(nq, npsi):
    qe = np.linspace(0, 1, nq + 1)
    pe = np.linspace(0, 2 * np.pi, npsi + 1)
    qc, pc = (qe[:-1] + qe[1:]) / 2, (pe[:-1] + pe[1:]) / 2
    # cell mass of h2 Haar = int (q/2) cos(2 psi) dq dpsi / (2 pi)
    mq = (qe[1:] ** 2 - qe[:-1] ** 2) / 4
    mp = (np.sin(2 * pe[1:]) - np.sin(2 * pe[:-1])) / 2 / (2 * np.pi)
    m = np.outer(mq, mp).ravel()
    rho = np.sqrt(np.repeat(qc, npsi)); psi = np.tile(pc, nq)
    P, N = np.where(m > 1e-15)[0], np.where(m < -1e-15)[0]
    a, b = m[P], -m[N]
    b *= a.sum() / b.sum()
    c = rho[P, None] * rho[None, N] * np.cos(psi[P, None] - psi[None, N]) + \
        np.sqrt(1 - rho[P, None] ** 2) * np.sqrt(1 - rho[None, N] ** 2)
    D = np.arccos(np.clip(c, -1, 1))
    nP, nN = len(P), len(N)
    rows = np.concatenate([np.repeat(np.arange(nP), nN), nP + np.tile(np.arange(nN), nP)])
    cols = np.concatenate([np.arange(nP * nN), np.arange(nP * nN)])
    A = coo_matrix((np.ones(2 * nP * nN), (rows, cols)), shape=(nP + nN, nP * nN)).tocsr()
    res = linprog(D.ravel(), A_eq=A, b_eq=np.concatenate([a, b]), bounds=(0, None), method="highs")
    return res.fun


for nq, npsi in ((8, 32), (12, 48), (16, 64)):
    print(f"nq={nq} npsi={npsi}: k_A ~ {kA(nq, npsi):.5f}", flush=True)
print(f"bracket: lower 0.05308 (test function), upper 1/(5 pi) = {1 / (5 * math.pi):.5f}")
