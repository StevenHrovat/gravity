"""PREREG run 3: CERTIFIED supremum of bound B1 (NOTE.md 2.3) over all Bingham conditional laws, and the certified windows.

What is certified. For kappa = 4 b_A / 3 (beta_F = 0) the single-link conditional law is rho = exp(u^T Q u)/Z on S^3 with Q of
eigenvalues kappa * s, s in Delta = {s >= 0, sum s = 6} (all of Delta occurs). NOTE.md 2.3 proves, for every such Q and every
moved staple a and direction b (M = sym(a b^T)):  ||(h2 - E h2) rho||_KR <= B1(Q) := 1/16 + sqrt(max(Pmax, Dmax) / 2), with
Pmax, Dmax explicit functions of the moments E[x^alpha] (|alpha| <= 2) of the Bingham laws with eigenvalues lambda and 2 lambda
(x = squared coordinates in the eigenbasis). This script encloses sup_{s in Delta} B1 by interval arithmetic:

* Bingham moments: power series with nonnegative terms (bingham.series, rig=True: rounding and truncation margins).
* Cells: boxes in (s1, s2, s3) (s4 = 6 - s1 - s2 - s3) covering the sorted simplex s1 >= s2 >= s3 >= s4 >= 0 (B1 is symmetric
  under permutations because the relaxation over M is). On each cell every quantity is a mean-value form ("MV"): its value at the
  cell centre (interval), its value over the cell and its gradient over the cell (intervals), propagated by the rules for +, -, x,
  1/x. The base series are increasing in every lambda_i, so their values and lambda-derivatives over a cell lie between the values
  at the lower and upper corners of the lambda-box. Enclosure over the cell: centre + sum_k grad_k [-r_k, r_k], intersected with
  the direct enclosure.
* Dmax: the top eigenvalue of Qd on the sum-zero subspace, bounded by `lam_max_perp` (exact integer basis, Weyl's
  inequality for the interval radius, Sylvester's criterion for the midpoint matrix; Gershgorin as fallback).
* Adaptive bisection until every cell satisfies 48 |b_A| B1_upper < 1 (or a minimum size is reached: then the run reports failure).
* Interval operations: round to nearest, then widen outward by one ulp (numpy.nextafter), as round 2's tree_cert.py.

Usage:  py cert_adjoint.py window b_A     (b_A signed; certify 48 |b_A| sup B1 < 1 at |kappa| = 4|b_A|/3 * (1 + 1e-12))
        py cert_adjoint.py sup b_A T      (certify sup B1 < T; T chosen just above the float supremum, for a tight value)
"""
import json
import math
import os
import sys
import time

os.environ.setdefault("CUDA_VISIBLE_DEVICES", "-1")
import numpy as np

import bingham as bg

INF = np.inf
HERE = os.path.dirname(os.path.abspath(__file__))
K = 48


def dn(x):
    return np.nextafter(x, -INF)


def up(x):
    return np.nextafter(x, INF)


class I:
    """interval arrays with outward rounding"""
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo = np.asarray(lo, dtype=np.float64)
        self.hi = self.lo if hi is None else np.asarray(hi, dtype=np.float64)

    @staticmethod
    def c(x):
        x = np.asarray(x, dtype=np.float64)
        return I(x, x)

    def __add__(self, o):
        o = o if isinstance(o, I) else I.c(o)
        return I(dn(self.lo + o.lo), up(self.hi + o.hi))

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, o):
        o = o if isinstance(o, I) else I.c(o)
        return I(dn(self.lo - o.hi), up(self.hi - o.lo))

    def __rsub__(self, o):
        return I.c(o) - self

    def __mul__(self, o):
        o = o if isinstance(o, I) else I.c(o)
        a, b, c, d = self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi
        return I(dn(np.minimum(np.minimum(a, b), np.minimum(c, d))), up(np.maximum(np.maximum(a, b), np.maximum(c, d))))

    __rmul__ = __mul__

    def recip(self):
        assert np.all(self.lo > 0), "reciprocal of an interval not > 0"
        return I(dn(1.0 / self.hi), up(1.0 / self.lo))

    def __truediv__(self, o):
        o = o if isinstance(o, I) else I.c(o)
        return self * o.recip()

    def mag(self):
        return np.maximum(np.abs(self.lo), np.abs(self.hi))

    def sq(self):
        """x^2 (tight: >= 0)"""
        m = self.mag()
        mig = np.where((self.lo <= 0) & (self.hi >= 0), 0.0, np.minimum(np.abs(self.lo), np.abs(self.hi)))
        return I(dn(mig * mig), up(m * m))

    def meet(self, o):
        return I(np.maximum(self.lo, o.lo), np.minimum(self.hi, o.hi))

    def __getitem__(self, k):
        return I(self.lo[k], self.hi[k])


class MV:
    """mean-value form on a batch of cells: c = value at the centre, v = value over the cell, g[k] = d/ds_k over the cell"""
    __slots__ = ("c", "v", "g")

    def __init__(self, c, v, g):
        self.c, self.v, self.g = c, v, g

    @staticmethod
    def const(x):
        z = I.c(0.0)
        return MV(I.c(x), I.c(x), [z, z, z])

    def __add__(self, o):
        o = o if isinstance(o, MV) else MV.const(o)
        return MV(self.c + o.c, self.v + o.v, [a + b for a, b in zip(self.g, o.g)])

    __radd__ = __add__

    def __neg__(self):
        return MV(-self.c, -self.v, [-a for a in self.g])

    def __sub__(self, o):
        o = o if isinstance(o, MV) else MV.const(o)
        return MV(self.c - o.c, self.v - o.v, [a - b for a, b in zip(self.g, o.g)])

    def __rsub__(self, o):
        return MV.const(o) - self

    def __mul__(self, o):
        if not isinstance(o, MV):
            o = I.c(o) if not isinstance(o, I) else o
            return MV(self.c * o, self.v * o, [a * o for a in self.g])
        return MV(self.c * o.c, self.v * o.v, [a * o.v + self.v * b for a, b in zip(self.g, o.g)])

    __rmul__ = __mul__

    def recip(self):
        rv = self.v.recip()
        return MV(self.c.recip(), rv, [-(a * rv * rv) for a in self.g])

    def __truediv__(self, o):
        if not isinstance(o, MV):
            o = I.c(o) if not isinstance(o, I) else o
            return self * o.recip()
        return self * o.recip()

    def enclose(self, r):
        """enclosure over the cells, r = (P, 3) half-widths"""
        e = self.c
        for k in range(3):
            e = e + self.g[k] * I(-r[:, k], r[:, k])
        return e.meet(self.v)


def lam_map(s, kap):
    """lambda(s) >= 0 (float), up to a shift: kap > 0: kap (s1, s2, s3, 6 - s1 - s2 - s3); kap < 0: |kap| (6 - s1, 6 - s2, 6 - s3,
    s1 + s2 + s3). d lambda / d s = kap J, J = [I; -1 -1 -1] in both cases."""
    s4 = 6 - s.sum(axis=1)
    if kap > 0:
        L = np.stack([s[:, 0], s[:, 1], s[:, 2], s4], axis=1) * kap
    else:
        L = np.stack([6 - s[:, 0], 6 - s[:, 1], 6 - s[:, 2], s.sum(axis=1)], axis=1) * (-kap)
    return L


def lam_box(slo, shi, kap):
    """componentwise lower/upper corners of the lambda-box of the cells (outward rounded), with a common nonnegative shift
    making every lower corner >= 0 (the moments' ratios are shift invariant; the shift is the same at both corners and at the
    centre of one cell)."""
    if kap > 0:
        lo = np.stack([slo[:, 0], slo[:, 1], slo[:, 2], 6 - shi.sum(axis=1)], axis=1)
        hi = np.stack([shi[:, 0], shi[:, 1], shi[:, 2], 6 - slo.sum(axis=1)], axis=1)
    else:
        lo = np.stack([6 - shi[:, 0], 6 - shi[:, 1], 6 - shi[:, 2], slo.sum(axis=1)], axis=1)
        hi = np.stack([6 - slo[:, 0], 6 - slo[:, 1], 6 - slo[:, 2], shi.sum(axis=1)], axis=1)
    k = abs(kap)
    shift = np.maximum(0.0, -lo.min(axis=1)) + 1e-9
    lo = dn(dn(lo + shift[:, None] - 1e-9) * k)
    hi = up(up(hi + shift[:, None] + 1e-9) * k)
    lo = np.maximum(lo, 0.0)
    return lo, hi, shift


def base_mv(alpha, lc, llo, lhi, kap, scale):
    """MV of S_alpha(scale * lambda(s)) on the cells: centre value from lc, value and gradient over the cell from the corners."""
    c = I(*bg.series(scale * lc, alpha, K, rig=True))
    v = I(bg.series(scale * llo, alpha, K, rig=True)[0], bg.series(scale * lhi, alpha, K, rig=True)[1])
    der = []
    for i in range(4):
        a2 = list(alpha); a2[i] += 1; a2 = tuple(a2)
        der.append(I(bg.series(scale * llo, a2, K, rig=True)[0], bg.series(scale * lhi, a2, K, rig=True)[1]))
    kf = I.c(scale * kap)
    g = [(der[k] - der[3]) * kf for k in range(3)]
    return MV(c, v, g)


_BAS = np.array([[1, 1, 1], [-1, 1, 1], [0, -2, 1], [0, 0, -3]], dtype=np.float64)  # orthogonal basis of 1-perp, norms^2 2, 6, 12
_NRM = np.array([2.0, 6.0, 12.0])


def lam_max_perp(Aenc):
    """rigorous upper bound, per cell, of the top eigenvalue on the sum-zero subspace of every symmetric matrix in the
    4x4 interval matrix Aenc (list of lists of I). Restrict to the basis _BAS (exact integers), normalise by sqrt(n_a n_b)
    (outward rounded), then Weyl: lam_max(M) <= lam_max(M_c) + ||M - M_c||_F; lam_max(M_c) <= mu is verified by Sylvester's
    criterion for mu I - M_c in interval arithmetic."""
    P = Aenc[0][0].lo.shape[0]
    G = [[None] * 3 for _ in range(3)]
    for a in range(3):
        for b in range(3):
            acc = I.c(np.zeros(P))
            for i in range(4):
                for j in range(4):
                    w = _BAS[i, a] * _BAS[j, b]
                    if w != 0:
                        acc = acc + Aenc[i][j] * w
            sq = np.sqrt(_NRM[a] * _NRM[b])
            G[a][b] = acc / I(dn(sq), up(sq))
    lo = np.stack([np.stack([G[a][b].lo for b in range(3)], -1) for a in range(3)], -2)
    hi = np.stack([np.stack([G[a][b].hi for b in range(3)], -1) for a in range(3)], -2)
    Mc = (lo + hi) / 2
    Mc = (Mc + np.swapaxes(Mc, -1, -2)) / 2
    rad = np.maximum(up(hi - Mc), up(Mc - lo))
    radF = up(np.sqrt(up(np.sum(up(rad * rad), axis=(-1, -2)) * (1 + 1e-14))))
    ev = np.linalg.eigvalsh(Mc)[:, -1]
    mu = ev + 1e-12 * (1 + np.abs(Mc).max(axis=(-1, -2))) + 1e-15
    # Sylvester for mu I - Mc with Mc as exact point matrix
    a = [[I.c((mu if i == j else 0.0) - Mc[:, i, j]) for j in range(3)] for i in range(3)]
    d1 = a[0][0]
    d2 = a[0][0] * a[1][1] - a[0][1] * a[1][0]
    d3 = (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1]) - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
          + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))
    okd = (d1.lo > 0) & (d2.lo > 0) & (d3.lo > 0)
    gersh = np.max(np.stack([Mc[:, i, i] + sum(np.abs(Mc[:, i, j]) for j in range(3) if j != i) for i in range(3)]), axis=0)
    mu = np.where(okd, mu, up(gersh * (1 + 1e-14) + 1e-300))
    return up(mu + radF)



def cell_bounds(slo, shi, kap):
    """for a batch of cells: upper bounds over each cell of B1, and of zeta, sigma1 = max E_lam[x_i], sigma2 = max E_2lam[x_i],
    V_h = sup_M Var(u^T M u) (||M||_F^2 = 1/2)."""
    P = slo.shape[0]
    sc = (slo + shi) / 2
    r = (shi - slo) / 2 + 1e-9
    llo, lhi, shift = lam_box(slo, shi, kap)
    lc = lam_map(sc, kap) + abs(kap) * shift[:, None]
    lc = np.maximum(lc, 0.0)
    out = {}
    mom = {}
    for scale in (1.0, 2.0):
        Z = base_mv((0, 0, 0, 0), lc, llo, lhi, kap, scale)
        iZ = Z.recip()
        m1 = [base_mv(tuple(1 if t == i else 0 for t in range(4)), lc, llo, lhi, kap, scale) * iZ for i in range(4)]
        m2 = [[None] * 4 for _ in range(4)]
        for i in range(4):
            for j in range(i, 4):
                a = [0] * 4; a[i] += 1; a[j] += 1
                m2[i][j] = base_mv(tuple(a), lc, llo, lhi, kap, scale) * iZ
                m2[j][i] = m2[i][j]
        mom[scale] = (Z, m1, m2)
    Z, m1, m2 = mom[1.0]
    Z2, n1, n2 = mom[2.0]
    zeta = Z2 / (Z * Z)
    C = [[m2[i][j] - m1[i] * m1[j] for j in range(4)] for i in range(4)]
    dm = [n1[i] - m1[i] for i in range(4)]
    C2 = [[n2[i][j] - n1[i] * n1[j] + dm[i] * dm[j] for j in range(4)] for i in range(4)]
    # pairs
    Pup = np.full(P, -INF)
    for i in range(4):
        for j in range(i + 1, 4):
            w = m2[i][j] * 24.0
            wm1 = w - 1.0
            p = wm1 * wm1 / 96.0 + ((zeta * n2[i][j]) * 2.0 - w * w / 12.0) / 24.0
            Pup = np.maximum(Pup, p.enclose(r).hi)
    # diagonal block: A = P_r Qd P_r with Qd = E^2/96 + P_r (zeta C2 - 12 C P_r C) P_r / 24, E = 12 P_r C P_r - P_r
    Pr = [[(1.0 if i == j else 0.0) - 0.25 for j in range(4)] for i in range(4)]

    def mm(A, B):
        out_ = [[None] * 4 for _ in range(4)]
        for i in range(4):
            for j in range(4):
                acc = None
                for k in range(4):
                    a, b = A[i][k], B[k][j]
                    if isinstance(a, float) and isinstance(b, float):
                        t = MV.const(a * b)
                    elif isinstance(a, float):
                        if a == 0.0:
                            continue
                        t = b * a
                    elif isinstance(b, float):
                        if b == 0.0:
                            continue
                        t = a * b
                    else:
                        t = a * b
                    acc = t if acc is None else acc + t
                out_[i][j] = acc if acc is not None else MV.const(0.0)
        return out_
    PCP = mm(mm(Pr, C), Pr)
    E = [[PCP[i][j] * 12.0 - Pr[i][j] for j in range(4)] for i in range(4)]
    EE = mm(E, E)
    CPC = mm(mm(C, Pr), C)
    inner = [[zeta * C2[i][j] - CPC[i][j] * 12.0 for j in range(4)] for i in range(4)]
    PIP = mm(mm(Pr, inner), Pr)
    Qd = [[EE[i][j] / 96.0 + PIP[i][j] / 24.0 for j in range(4)] for i in range(4)]
    Dup = lam_max_perp([[Qd[i][j].enclose(r) for j in range(4)] for i in range(4)])
    X = np.maximum(np.maximum(Pup, Dup), 0.0)
    B1 = up(1.0 / 16.0 + up(np.sqrt(up(X / 2.0))) * (1 + 1e-15))
    out["B1"] = B1
    out["P"] = Pup
    out["D"] = Dup
    out["zeta"] = zeta.enclose(r).hi
    out["sigma1"] = np.max(np.stack([m1[i].enclose(r).hi for i in range(4)]), axis=0)
    out["sigma2"] = np.max(np.stack([n1[i].enclose(r).hi for i in range(4)]), axis=0)
    vpair = np.max(np.stack([m2[i][j].enclose(r).hi for i in range(4) for j in range(i + 1, 4)]), axis=0)
    vdiag = lam_max_perp([[C[i][j].enclose(r) for j in range(4)] for i in range(4)])
    out["Vh"] = np.maximum(vpair, up(vdiag / 2))
    return out


def feasible(slo, shi):
    """cells that can meet the sorted simplex s1 >= s2 >= s3 >= s4 = 6 - s1 - s2 - s3 >= 0 (necessary conditions)"""
    return ((shi[:, 0] >= slo[:, 1]) & (shi[:, 1] >= slo[:, 2]) & (shi[:, 2] >= 6 - shi.sum(axis=1))
            & (slo.sum(axis=1) <= 6))


def certify(bA, h0=0.25, hmin=2e-3, batch=4000, log=print, target=None):
    kap = 4 * bA / 3 * (1 + 1e-12)
    if target is None:
        target = 1.0 / (48 * abs(bA))
    g1 = np.arange(1.5, 6.0, h0)
    g2 = np.arange(0.0, 3.0, h0)
    g3 = np.arange(0.0, 2.0, h0)
    G = np.array(np.meshgrid(g1, g2, g3, indexing="ij")).reshape(3, -1).T
    slo, shi = G, G + h0
    keep = feasible(slo, shi)
    slo, shi = slo[keep], shi[keep]
    done = {k: -INF for k in ("B1", "P", "D", "zeta", "sigma1", "sigma2", "Vh")}
    ncells, nevals, t0 = 0, 0, time.time()
    worst = None
    while len(slo):
        nxt_lo, nxt_hi = [], []
        for b0 in range(0, len(slo), batch):
            lo_, hi_ = slo[b0:b0 + batch], shi[b0:b0 + batch]
            o = cell_bounds(lo_, hi_, kap)
            nevals += len(lo_)
            ok = o["B1"] < target
            for k in done:
                if np.any(ok):
                    done[k] = max(done[k], float(o[k][ok].max()))
            if np.any(ok):
                i = int(np.argmax(np.where(ok, o["B1"], -INF)))
                if worst is None or o["B1"][i] > worst[0]:
                    worst = (float(o["B1"][i]), lo_[i].tolist(), hi_[i].tolist())
            ncells += int(ok.sum())
            bad = ~ok
            if np.any(bad):
                bl, bh = lo_[bad], hi_[bad]
                w = bh - bl
                if np.any(w.max(axis=1) < hmin):
                    j = int(np.argmax(o["B1"]))
                    log(f"  FAIL: cell {lo_[j]}..{hi_[j]} has B1 <= {o['B1'][j]:.6f} >= target {target:.6f} at min size")
                    return None
                ax = np.argmax(w, axis=1)
                mid = bl[np.arange(len(bl)), ax] + w[np.arange(len(bl)), ax] / 2
                h1 = bh.copy(); h1[np.arange(len(bl)), ax] = mid
                l2 = bl.copy(); l2[np.arange(len(bl)), ax] = mid
                cl = np.concatenate([bl, l2]); ch = np.concatenate([h1, bh])
                f = feasible(cl, ch)
                nxt_lo.append(cl[f]); nxt_hi.append(ch[f])
        slo = np.concatenate(nxt_lo) if nxt_lo else np.zeros((0, 3))
        shi = np.concatenate(nxt_hi) if nxt_hi else np.zeros((0, 3))
        log(f"  pass: {ncells} cells certified, {len(slo)} to refine, {nevals} evaluations, {time.time() - t0:.0f}s")
    res = dict(b_A=bA, kappa=kap, target=target, cells=ncells, evaluations=nevals, secs=time.time() - t0, worst_cell=worst,
               **{k + "_sup": v for k, v in done.items()})
    res["column_sup"] = 48 * abs(bA) * done["B1"]
    return res


def main():
    mode = sys.argv[1]
    if mode in ("window", "sup"):
        bA = float(sys.argv[2])
        res = certify(bA, target=float(sys.argv[3]) if mode == "sup" else None)
        path = os.path.join(HERE, "cert_window.json")
        store = json.load(open(path)) if os.path.exists(path) else {}
        if res is None:
            print(f"b_A = {bA}: NOT certified")
            store[f"{mode}{bA:+.4f}"] = dict(certified=False)
        else:
            print(f"b_A = {bA}: certified sup B1 <= {res['B1_sup']:.6f}; column 48|b_A| B1 <= {res['column_sup']:.6f} < 1;"
                  f" zeta <= {res['zeta_sup']:.5f}, sigma1 <= {res['sigma1_sup']:.5f}, sigma2 <= {res['sigma2_sup']:.5f},"
                  f" Vh <= {res['Vh_sup']:.5f}; {res['cells']} cells, {res['secs']:.0f}s")
            store[f"{mode}{bA:+.4f}"] = dict(certified=True, mode=mode, **res)
        json.dump(store, open(path, "w"), indent=1)


if __name__ == "__main__":
    main()
