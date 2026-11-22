"""PREREG run 1: checks of the analytic claims (float / Monte Carlo, seconds).
(a) k_A = E_Haar[|u_a u_b| min(arcsin|u_a|, arcsin|u_b|)] = 1/16 (MC on S^3, and polar quadrature on the unit disk, where the
    joint law of (u_a, u_b) is uniform).
(b) the symmetric formula at the aligned configuration Q = 6 kappa a a^T against c2a's transport LP (kA_bingham.log:
    0.06751 at b_A = 0.1, 0.07355 at 0.26, 0.07491 at 1/3, 0.07419 at 0.5; the LP is ~0.0002 low at the uniform point).
(c) the series moments against Monte Carlo; B1 at the uniform point equals 1/16.
"""
import math
import os

os.environ.setdefault("CUDA_VISIBLE_DEVICES", "-1")
import numpy as np
from scipy import integrate
from scipy.special import i0

import bingham as bg


def wfun(x, y):
    return np.abs(x * y) * np.minimum(np.arcsin(np.minimum(np.abs(x), 1)), np.arcsin(np.minimum(np.abs(y), 1)))


def sym_formula(qa, qb, q3, q4):
    """E_rho[w(u_a, u_b)] for rho ~ exp(qa u_a^2 + qb u_b^2 + q3 u_3^2 + q4 u_4^2) (a, b eigenvectors): 2D polar quadrature."""
    def wt(r, t):
        x, y = r * math.cos(t), r * math.sin(t)
        s = 1 - r * r
        return math.exp(qa * x * x + qb * y * y + (q3 + q4) * s / 2) * i0((q3 - q4) * s / 2) * r
    num = integrate.dblquad(lambda r, t: wfun(np.array(r * math.cos(t)), np.array(r * math.sin(t))) * wt(r, t),
                            0, 2 * math.pi, 0, 1, epsabs=1e-12, epsrel=1e-10)[0]
    den = integrate.dblquad(wt, 0, 2 * math.pi, 0, 1, epsabs=1e-12, epsrel=1e-10)[0]
    return num / den


if __name__ == "__main__":
    rng = np.random.default_rng(7)
    n = 4_000_000
    u = rng.normal(size=(n, 4)); u /= np.linalg.norm(u, axis=1, keepdims=True)
    w = wfun(u[:, 0], u[:, 1])
    print(f"(a) k_A MC: {w.mean():.6f} +- {w.std() / math.sqrt(n):.6f}   (1/16 = {1 / 16:.6f})")
    print(f"(a) k_A disk quadrature: {sym_formula(0, 0, 0, 0):.10f}")
    # lower bound check: the same function as a test function, integrated against h2 Haar (h2 = u_a u_b)
    phi = np.sign(u[:, 0] * u[:, 1]) * np.minimum(np.arcsin(np.abs(u[:, 0])), np.arcsin(np.abs(u[:, 1])))
    print(f"(a) int phi* h2 dHaar (MC): {np.mean(phi * u[:, 0] * u[:, 1]):.6f}")
    for bA, lp in ((0.1, 0.06751), (0.26, 0.07355), (1 / 3, 0.07491), (0.5, 0.07419)):
        k = 4 * bA / 3
        print(f"(b) aligned b_A = {bA:.3f}: exact formula {sym_formula(6 * k, 0, 0, 0):.5f}   c2a LP {lp:.5f}")
    # (c) series vs MC
    lam = np.array([[1.3, 0.2, 0.0, 0.7]])
    Z, m1, m2 = bg.moments_float(lam)
    x = u ** 2
    wt = np.exp(x @ lam[0])
    print(f"(c) Z: series {Z[0]:.6f}  MC {wt.mean():.6f};  E[x1]: {m1[0, 0]:.5f} vs {np.mean(wt * x[:, 0]) / wt.mean():.5f};"
          f"  E[x1 x4]: {m2[0, 0, 3]:.6f} vs {np.mean(wt * x[:, 0] * x[:, 3]) / wt.mean():.6f}")
    lo, hi = bg.series(lam, (1, 0, 0, 1), rig=True)
    print(f"(c) rigorous enclosure S_(1,0,0,1): [{lo[0]:.15g}, {hi[0]:.15g}]")
    N, *_ = bg.b1_float(np.zeros((1, 4)))
    print(f"(c) B1 at Haar: {N[0]:.12f} (1/16 = 0.0625)")
