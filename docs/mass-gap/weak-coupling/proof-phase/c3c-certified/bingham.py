"""Bingham moments on S^3 as power series (shared by checks.py, explore.py, cert_adjoint.py).

u uniform on S^3  <=>  x = (u_1^2, ..., u_4^2) ~ Dirichlet(1/2, 1/2, 1/2, 1/2), with exact moments
  E[x^g] = prod_i (1/2)_{g_i} / (2)_{|g|}            ((a)_n the rising factorial).
For lambda >= 0 (componentwise) and a multi-index alpha:
  S_alpha(lambda) = E_Haar[x^alpha e^{lambda . x}] = sum_beta lambda^beta / beta! * prod_i (1/2)_{alpha_i + beta_i} / (2)_{|alpha| + |beta|}
is a series of NONNEGATIVE terms, increasing in every lambda_i. It is evaluated as the product of four univariate polynomials
p_i(t) = sum_b lambda_i^b (1/2)_{alpha_i + b} / b! t^b (truncated at degree K), whose degree-n coefficient is divided by
(2)_{|alpha| + n} and summed.

Rigour (used by cert_adjoint.py): every term is a nonnegative float computed from nonnegative inputs by at most
4 (K + 1) + 8 multiplications/divisions and additions along any chain, so the computed sum is within a relative 2^-53 * 8 (K + 2)
(<= 1e-13 for K <= 60) of the exact truncated sum (standard error analysis of sums and products of nonnegative numbers);
the coefficient tables are rounded from 50-digit mpmath values (relative error <= 2^-53). Tail beyond degree K:
  sum_{n > K} E[x^alpha (lambda.x)^n] / n! <= sum_{n > K} L^n / n! <= L^{K+1} / (K+1)! / (1 - L / (K + 2)),  L = max_i lambda_i,
because lambda . x <= max_i lambda_i and x^alpha <= 1.  `series(..., rig=True)` returns (lo, hi) with these margins.
"""
import itertools
import math

import mpmath as mp
import numpy as np

mp.mp.dps = 50
REL = 1e-12          # generous a-priori relative rounding bound (see docstring: <= 1e-13 needed)
_TAB = {}


def coef_table(amax, K):
    """T[a][b] = (1/2)_{a + b} / b!  for a <= amax, b <= K (float, from 50-digit values); D[n] = 1 / (2)_n, n <= K + 2 amax + 8."""
    key = (amax, K)
    if key in _TAB:
        return _TAB[key]
    T = np.zeros((amax + 1, K + 1))
    for a in range(amax + 1):
        for b in range(K + 1):
            T[a, b] = float(mp.rf(mp.mpf(1) / 2, a + b) / mp.factorial(b))
    nD = K + 2 * amax + 9
    D = np.array([float(1 / mp.rf(2, n)) for n in range(nD)])
    _TAB[key] = (T, D)
    return T, D


def series(lam, alpha, K=48, rig=False):
    """S_alpha(lam) for lam of shape (P, 4), lam >= 0. Float value, or (lo, hi) rigorous enclosure if rig."""
    lam = np.asarray(lam, dtype=np.float64)
    assert np.all(lam >= 0)
    amax = max(4, max(alpha))
    T, D = coef_table(amax, K)
    P = lam.shape[0]
    bpow = np.arange(K + 1)
    polys = []
    for i in range(4):
        with np.errstate(divide="ignore", invalid="ignore"):
            pw = np.where(bpow[None, :] == 0, 1.0, lam[:, i:i + 1] ** bpow[None, :])
        polys.append(pw * T[alpha[i]][None, :])
    c = polys[0]
    for q in polys[1:]:
        # truncated convolution c * q up to degree K, vectorised over points
        out = np.zeros((P, K + 1))
        for b in range(K + 1):
            out[:, b:] += c[:, :K + 1 - b] * q[:, b:b + 1]
        c = out
    A = sum(alpha)
    val = (c * D[A:A + K + 1][None, :]).sum(axis=1)
    if not rig:
        return val
    L = lam.max(axis=1)
    assert np.all(L < K / 2)
    # L^{K+1}/(K+1)!/(1 - L/(K+2)), evaluated through logarithms with a factor-2 safety margin (the tail is < 1e-25 here,
    # so only its being an upper bound matters, not its accuracy)
    with np.errstate(divide="ignore"):
        lt = (K + 1) * np.log(np.where(L > 0, L, 1.0)) - math.lgamma(K + 2)
    tail = np.where(L > 0, 2.0 * np.exp(lt) / (1 - L / (K + 2)), 0.0)
    lo = val * (1 - REL)
    hi = (val + tail) * (1 + REL)
    return lo, hi


def multi_indices(deg):
    """all alpha in N^4 with |alpha| <= deg"""
    return [a for a in itertools.product(range(deg + 1), repeat=4) if sum(a) <= deg]


def moments_float(lam, K=48):
    """Z, m1 (P,4), m2 (P,4,4) of the Bingham law exp(lam.x)/Z (float)."""
    P = lam.shape[0]
    Z = series(lam, (0, 0, 0, 0), K)
    m1 = np.zeros((P, 4))
    m2 = np.zeros((P, 4, 4))
    for i in range(4):
        e = [0] * 4; e[i] = 1
        m1[:, i] = series(lam, tuple(e), K) / Z
        for j in range(i, 4):
            e2 = [0] * 4; e2[i] += 1; e2[j] += 1
            v = series(lam, tuple(e2), K) / Z
            m2[:, i, j] = v; m2[:, j, i] = v
    return Z, m1, m2


def b1_float(lam, K=48):
    """Bound B1 (NOTE.md 2.3) on N_A = sup_M ||(h2 - m) rho||_KR at the Bingham law with eigenvalues lam (P,4), float.
    Returns (N_bar, Pmax, Dmax, zeta, sigma2max, Vh)."""
    Z, m1, m2 = moments_float(lam, K)
    Z2, n1, n2 = moments_float(2 * lam, K)
    zeta = Z2 / Z ** 2
    C = m2 - m1[:, :, None] * m1[:, None, :]
    dm = n1 - m1
    C2 = n2 - n1[:, :, None] * n1[:, None, :] + dm[:, :, None] * dm[:, None, :]
    Pm = np.full(lam.shape[0], -np.inf)
    for i in range(4):
        for j in range(i + 1, 4):
            w = 24 * m2[:, i, j]
            p = (w - 1) ** 2 / 96 + (2 * zeta * n2[:, i, j] - w ** 2 / 12) / 24
            Pm = np.maximum(Pm, p)
    # basis of the sum-zero subspace
    B = np.array([[1, -1, 0, 0], [1, 1, -2, 0], [1, 1, 1, -3]], dtype=float)
    B = (B / np.linalg.norm(B, axis=1, keepdims=True)).T  # 4x3
    Pr = np.eye(4) - np.ones((4, 4)) / 4
    E = 12 * np.einsum("ij,pjk,kl->pil", Pr, C, Pr) - Pr[None]
    Qd = np.einsum("pij,pjk->pik", E, E) / 96 + np.einsum("ij,pjk,kl->pil", Pr,
                                                            zeta[:, None, None] * C2 - 12 * np.einsum("pij,jk,pkl->pil", C, Pr, C),
                                                            Pr) / 24
    Q3 = np.einsum("ia,pij,jb->pab", B, Qd, B)
    Dm = np.linalg.eigvalsh(Q3)[:, -1]
    N = 1 / 16 + np.sqrt(0.5 * np.maximum(np.maximum(Pm, Dm), 0))
    s2 = n1.max(axis=1)
    Vh = np.maximum(np.max(np.where(np.eye(4)[None] > 0, -np.inf, m2), axis=(1, 2)),
                    0.5 * np.linalg.eigvalsh(np.einsum("ia,pij,jb->pab", B, C, B))[:, -1])
    return N, Pm, Dm, zeta, s2, Vh
