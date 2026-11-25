"""Round 2 attempt A: float (non-rigorous) evaluator of the tree-flow upper bound for 2D compact U(1) thin squares.

Design tool for the certified run (`tree_cert.py`). Same recursion, plain float64, no enclosures.
Notation: PREREG.md. Grid x_k = k w, w = 2 pi / G (k = 0..G-1); sums of angles are taken mod 2 pi on this grid.

Usage: py tree_float.py beta l [G] [shape]      prints k(P_i) per position, k(D), gamma
"""
import os
import sys
import time

os.environ.setdefault("CUDA_VISIBLE_DEVICES", "-1")
import numpy as np
from scipy.special import ive


class Fourier:
    def __init__(self, beta, G):
        self.beta, self.G = beta, G
        self.w = 2 * np.pi / G
        self.x = np.arange(G) * self.w
        n = np.arange(1, 60)
        r = ive(n, beta) / ive(0, beta)
        self.n, self.r = n[r > 1e-300], r[r > 1e-300]
        self.C = np.cos(np.outer(self.n, self.x))
        self.Sn = np.sin(np.outer(self.n, self.x))
        self._g = {}

    def g(self, m):
        """(density, derivative) of the sum of m iid von Mises angles on the grid."""
        if m not in self._g:
            c = self.r ** m
            k = max(1, int(np.sum(c > 1e-18)))
            c, n = c[:k], self.n[:k]
            self._g[m] = ((1 + 2 * c @ self.C[:k]) / (2 * np.pi), (-2 * (c * n) @ self.Sn[:k]) / (2 * np.pi))
        return self._g[m]


def node_cost(F, mA, hA, mB, hB):
    """h(S) on the grid for a node with children A (m_A vars, weight hA(y) = h_A + e_A) and B (weight hB(t), t = S - y).
    Returns h (array over S) and the chosen c (array over S)."""
    G, w = F.G, F.w
    gA, _ = F.g(mA)
    gB, gBd = F.g(mB)
    gm, gmd = F.g(mA + mB)
    k = np.arange(G)
    idx = (k[:, None] - k[None, :]) % G  # S - y
    rho = gA[None, :] * gB[idx] / gm[:, None]
    drho = gA[None, :] * gBd[idx] / gm[:, None] - rho * (gmd / gm)[:, None]
    # G_S(y) = - int_0^y d_S rho (trapezoid on the grid)
    cum = np.concatenate([np.zeros((G, 1)), np.cumsum(0.5 * (drho[:, 1:] + drho[:, :-1]) * w, axis=1)], axis=1)
    Gs = -cum
    wA = w * np.broadcast_to(hA[None, :], (G, G))
    wB = w * hB[idx]
    # minimise over c: sum wA |c + Gs| + wB |c - (rho - Gs)|  -> weighted median of {-Gs} u {rho - Gs}
    bp = np.concatenate([-Gs, rho - Gs], axis=1)
    wt = np.concatenate([wA, wB], axis=1)
    o = np.argsort(bp, axis=1)
    bps = np.take_along_axis(bp, o, 1)
    cw = np.cumsum(np.take_along_axis(wt, o, 1), axis=1)
    half = cw[:, -1:] / 2
    pos = np.argmax(cw >= half, axis=1)
    c = bps[k, pos]
    h = (wA * np.abs(Gs + c[:, None]) + wB * np.abs(rho - Gs - c[:, None])).sum(1)
    return h, c


def shells(l, i):
    """Rest variables around p0 = plaquette (i, 0), grouped by Manhattan distance r of their plaquette: list of lists of routing
    costs (plaquette: r; face link: r + 1). f_i excluded."""
    sh = {}
    for a in range(l):
        for b in range(l):
            r = abs(a - i) + b
            sh.setdefault(r, []).append(r)
    faces = [abs(j - i) for j in range(l) if j != i] + [abs(j - i) + l - 1 for j in range(l)] + \
            [i + j for j in range(l)] + [(l - 1 - i) + j for j in range(l)]
    for r in faces:
        sh.setdefault(r, []).append(r + 1)
    return [sorted(sh[r], reverse=True) for r in sorted(sh)]


def chain(F, costs_far_first, zero):
    """Caterpillar over a list of subtrees given far first: each item (m, h) with h = h_child + e on the grid.
    Returns (m_total, h_total)."""
    # build from the near end upwards: acc = nearest; then acc = (next farther, acc)
    acc_m, acc_h = costs_far_first[-1]
    for mi, hi in reversed(costs_far_first[:-1]):
        hn, _ = node_cost(F, mi, hi, acc_m, acc_h)
        acc_m, acc_h = mi + acc_m, hn
    return acc_m, acc_h


def kP(F, l, i, shape="single"):
    zero = np.zeros(F.G)
    if shape == "single":  # one caterpillar over all Rest variables, sorted by routing cost, far first
        costs = sorted(sum(shells(l, i), []), reverse=True)
        mR, hR = chain(F, [(1, zero + c) for c in costs], zero)
        return node_cost(F, 1, zero, mR, 1 + hR)[0]
    sh = shells(l, i)
    items = []
    for costs in reversed(sh):  # far shell first
        leaves = [(1, zero + c) for c in costs]  # leaf: h = 0, edge = routing cost
        if len(leaves) == 1:
            items.append(leaves[0])
        else:
            m, h = chain(F, leaves, zero)
            items.append((m, h))
    mR, hR = chain(F, items, zero)
    assert mR == l * l + 4 * l - 1
    hroot, _ = node_cost(F, 1, zero, mR, 1 + hR)
    return hroot  # over Phi


def kD(F, l):
    """3 * int rho_Phi(u) R(2 beta |cos(u/2)|) du, sup over Phi."""
    N = l * l + 4 * l
    g2, _ = F.g(2)
    gr, _ = F.g(N - 2)
    gN, _ = F.g(N)
    u = F.x
    kap = 2 * F.beta * np.abs(np.cos(u / 2))
    # R(kappa) = E_vM(kappa)[sign cos x] = (4/pi) sum_k (-1)^k (I_{2k+1}/I_0)(kappa) / (2k+1)
    R = np.zeros_like(u)
    for kk in range(0, 200):
        R += (4 / np.pi) * (-1) ** kk * ive(2 * kk + 1, kap) / ive(0, kap) / (2 * kk + 1)
    G = F.G
    k = np.arange(G)
    idx = (k[:, None] - k[None, :]) % G
    rho = g2[None, :] * gr[idx] / gN[:, None]
    val = (rho * R[None, :]).sum(1) * F.w
    return 3 * val


def main():
    beta = float(sys.argv[1])
    l = int(sys.argv[2])
    G = int(sys.argv[3]) if len(sys.argv) > 3 else 512
    F = Fourier(beta, G)
    t0 = time.time()
    kd = kD(F, l)
    kps = []
    for i in range((l + 1) // 2):
        h = kP(F, l, i)
        kps.append(h.max())
        print("i=%d kP=%.4f (min over Phi %.4f)" % (i, h.max(), h.min()), flush=True)
    kfull = [kps[min(i, l - 1 - i)] for i in range(l)]
    gam = (2 * sum(kfull) + 2 * (l - 1) * kd.max() + 4 * kfull[0]) / (l * (l + 1))
    print("beta=%g l=%d G=%d kD=%.4f gamma=%.4f (%.0fs)" % (beta, l, G, kd.max(), gam, time.time() - t0))


if __name__ == "__main__":
    main()
