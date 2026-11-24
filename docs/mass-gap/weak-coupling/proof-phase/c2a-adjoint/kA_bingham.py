"""Nonlinear indication for the W1 adjoint coefficient (NOTE.md 2.4): KR norm of the derivative of a Bingham conditional law
rho ~ exp(u^T Q u) along one moved staple, at the aligned configuration (six equal staples a: Q = 6 kappa a a^T,
kappa = 4 b_A / 3, b_F = 0), per unit coupling: k_A(Q) = ||(h2 - E h2) rho||_KR with h2 = <u,a><u,b>. Same quotient LP as kA_lp.py
(midpoint cell masses; an estimate). A lower bound on the supremum over configurations, not an upper bound."""
import math
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix


def kA_rho(bA, nq=16, npsi=64):
    qe = np.linspace(0, 1, nq + 1); pe = np.linspace(0, 2 * np.pi, npsi + 1)
    qc, pc = (qe[:-1] + qe[1:]) / 2, (pe[:-1] + pe[1:]) / 2
    Q, P = np.meshgrid(qc, pc, indexing="ij")
    # a = (y1 + y2)/sqrt2 direction: <u,a>^2 = q (1 + sin 2 psi) / 2; b = (y1 - y2)/sqrt2: <u,a><u,b> = q cos(2 psi)/2
    kappa = 4 * bA / 3
    w = np.exp(6 * kappa * Q * (1 + np.sin(2 * P)) / 2)
    cell = (1 / nq) * (1 / npsi)
    w = w / (w.sum() * cell)
    h2 = Q * np.cos(2 * P) / 2
    h2 = h2 - (h2 * w).sum() * cell
    m = (h2 * w * cell).ravel()
    rho = np.sqrt(Q.ravel()); psi = P.ravel()
    Pi, Ni = np.where(m > 1e-15)[0], np.where(m < -1e-15)[0]
    a, b = m[Pi], -m[Ni]; b *= a.sum() / b.sum()
    c = rho[Pi, None] * rho[None, Ni] * np.cos(psi[Pi, None] - psi[None, Ni]) + \
        np.sqrt(1 - rho[Pi, None] ** 2) * np.sqrt(1 - rho[None, Ni] ** 2)
    D = np.arccos(np.clip(c, -1, 1))
    nP, nN = len(Pi), len(Ni)
    rows = np.concatenate([np.repeat(np.arange(nP), nN), nP + np.tile(np.arange(nN), nP)])
    cols = np.concatenate([np.arange(nP * nN)] * 2)
    A = coo_matrix((np.ones(2 * nP * nN), (rows, cols)), shape=(nP + nN, nP * nN)).tocsr()
    return linprog(D.ravel(), A_eq=A, b_eq=np.concatenate([a, b]), bounds=(0, None), method="highs").fun


k0 = kA_rho(0.0)
for bA in (0.0, 0.1, 1 / 3, 0.5):
    k = kA_rho(bA)
    print(f"b_A = {bA:.3f}: k_A(aligned) ~ {k:.5f} (ratio to uniform point {k / k0:.3f}); column 18 (8/3) k b_A = {48 * k * bA:.3f}")
