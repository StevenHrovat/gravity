"""Round 2 attempt A: CERTIFIED (interval arithmetic) upper bounds on the W-form influence coefficients of 2D compact U(1) thin
squares, and the resulting GDS coefficient gamma(l). Method and notation: PREREG.md, NOTE.md ("Certificate").

Every quantity is an interval [lo, hi] of float64 arrays. Basic operations (+ - * /) are computed in round-to-nearest and then widened
outward by one ulp (numpy.nextafter), which encloses the exact result (IEEE-754: the rounding error of a basic operation is at most
half an ulp). Sums of many terms use the a-priori bound n * 2^-52 * sum|x| for the accumulated rounding error. Transcendental inputs
(I_n(beta)/I_0(beta) and its powers, cos and sin at the grid angles, the von Mises rigid-shift rate R(kappa)) are computed with
mpmath at 40 digits and rounded outward. Fourier tails beyond n = NT are bounded by I_n(beta) <= (beta/2)^n e^{beta^2/4} / n!.

Grid: G cells of width w = 2 pi / G on the circle; the half-grid x_j = j w / 2 (j = 0..2G-1) carries all point evaluations
(cell K = [K w, (K + 1) w], centre at half-grid index 2K + 1).

Usage:
  py tree_cert.py P beta l i G        -> certified k(P_i) (sup over all Phi), appended to cert_<beta>_<l>.json
  py tree_cert.py D beta l G          -> certified k(D)
  py tree_cert.py gamma beta l        -> certified gamma(l) from the stored k's (needs all positions and D)
"""
import json
import os
import sys
import time

os.environ.setdefault("CUDA_VISIBLE_DEVICES", "-1")
import mpmath as mp
import numpy as np

mp.mp.dps = 40
HERE = os.path.dirname(os.path.abspath(__file__))
INF = np.inf
EPS = 2.0 ** -52
NT = 40  # Fourier terms kept


# ---------------------------------------------------------------- interval arithmetic (outward rounding)

def dn(x):
    return np.nextafter(x, -INF)


def up(x):
    return np.nextafter(x, INF)


class I:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        lo = np.asarray(lo, dtype=np.float64)
        self.lo = lo
        self.hi = lo if hi is None else np.asarray(hi, dtype=np.float64)

    @staticmethod
    def exact(x):
        x = np.asarray(x, dtype=np.float64)
        return I(x, x)

    def __add__(self, o):
        o = o if isinstance(o, I) else I.exact(o)
        return I(dn(self.lo + o.lo), up(self.hi + o.hi))

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, o):
        o = o if isinstance(o, I) else I.exact(o)
        return I(dn(self.lo - o.hi), up(self.hi - o.lo))

    def __rsub__(self, o):
        return I.exact(o) - self

    def __mul__(self, o):
        o = o if isinstance(o, I) else I.exact(o)
        a, b, c, d = self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi
        return I(dn(np.minimum(np.minimum(a, b), np.minimum(c, d))), up(np.maximum(np.maximum(a, b), np.maximum(c, d))))

    __rmul__ = __mul__

    def recip(self):
        assert np.all(self.lo > 0) or np.all(self.hi < 0), "division by an interval containing 0"
        return I(dn(1.0 / self.hi), up(1.0 / self.lo))

    def __truediv__(self, o):
        o = o if isinstance(o, I) else I.exact(o)
        return self * o.recip()

    def mag(self):
        """upper bound of |x|"""
        return np.maximum(np.abs(self.lo), np.abs(self.hi))

    def widen(self, r):
        """[lo - r, hi + r], r >= 0 an upper bound (float array)"""
        return I(dn(self.lo - r), up(self.hi + r))

    def __getitem__(self, k):
        return I(self.lo[k], self.hi[k])


def sum_up(x, axis):
    """rigorous upper bound of the exact sum of a float array x along axis"""
    n = x.shape[axis]
    s = np.sum(x, axis=axis)
    return up(s + up(n * EPS * np.sum(np.abs(x), axis=axis)) + 1e-300)


def sum_dn(x, axis):
    n = x.shape[axis]
    s = np.sum(x, axis=axis)
    return dn(s - up(n * EPS * np.sum(np.abs(x), axis=axis)) - 1e-300)


def isum(x, axis):
    return I(sum_dn(x.lo, axis), sum_up(x.hi, axis))


def icumsum(x, axis):
    """inclusive cumulative sum with rigorous enclosure"""
    n = x.lo.shape[axis]
    slo, shi = np.cumsum(x.lo, axis=axis), np.cumsum(x.hi, axis=axis)
    elo = n * EPS * np.cumsum(np.abs(x.lo), axis=axis)
    ehi = n * EPS * np.cumsum(np.abs(x.hi), axis=axis)
    return I(dn(slo - up(elo) - 1e-300), up(shi + up(ehi) + 1e-300))


def mpI(x):
    """outward float interval of an mpmath number"""
    f = float(x)
    return dn(f), up(f)


# ---------------------------------------------------------------- Fourier data of sums of von Mises angles

class Model:
    def __init__(self, beta, G):
        self.beta, self.G = beta, G
        self.w = 2 * np.pi / G  # float (heuristic parts only)
        self.wI = I(*mpI(2 * mp.pi / G))  # exact cell width enclosed
        self.wh = float(self.wI.hi)
        b = mp.mpf(beta)
        self.rn = [mp.besseli(n, b) / mp.besseli(0, b) for n in range(1, NT + 1)]
        # tail bound: sum_{n > NT} n^5 r_n  (>= sum n^k r_n^m for k <= 5, m >= 1)
        tail = mp.mpf(0)
        for n in range(NT + 1, 400):
            tail += mp.mpf(n) ** 5 * mp.e ** (b * b / 4) * (b / 2) ** n / mp.factorial(n)
        tail *= 2  # the terms beyond 400 are below a geometric series of ratio < 1/2 starting below the last term
        self.tail = float(tail) * 2 + 1e-300
        # trig table on the half grid: angle j pi / G
        j2 = 2 * G
        cl, ch, sl, sh = (np.empty(j2) for _ in range(4))
        for j in range(j2):
            a = mp.pi * j / G
            cl[j], ch[j] = mpI(mp.cos(a))
            sl[j], sh[j] = mpI(mp.sin(a))
        self.cos, self.sin = I(cl, ch), I(sl, sh)
        nn = np.arange(1, NT + 1)
        self.tab = (np.outer(nn, np.arange(j2)) % j2)  # index of n x_j in the half-grid table
        self._f = {}

    def coef(self, m):
        lo, hi = np.empty(NT), np.empty(NT)
        for k, r in enumerate(self.rn):
            lo[k], hi[k] = mpI(r ** m)
        lo = np.maximum(lo, 0.0)
        return I(lo, hi)

    def f(self, m):
        """dict: 'val': [g, g', g'', g'''] as intervals on the half grid; 'M': upper bounds of sup|g^(k)|, k = 0..5;
        'inf': lower bound of inf g"""
        if m in self._f:
            return self._f[m]
        c = self.coef(m)
        nn = np.arange(1, NT + 1, dtype=np.float64)
        vals = []
        for k in range(4):
            ck = c * I.exact(nn ** k)  # n^k r_n^m
            trig = self.cos if k % 2 == 0 else self.sin
            T = I(trig.lo[self.tab], trig.hi[self.tab])  # (NT, 2G)
            terms = I(ck.lo[:, None], ck.hi[:, None]) * T
            s = isum(terms, axis=0).widen(self.tail)
            # g = (1 + 2 s0)/2pi, g' = -2 s1/2pi, g'' = -2 s2/2pi, g''' = 2 s3/2pi
            sign = [1, -1, -1, 1][k]
            v = s * I.exact(2.0)
            if sign < 0:
                v = -v
            if k == 0:
                v = v + 1.0
            v = v * I(dn(1 / (2 * np.pi)), up(1 / (2 * np.pi)))
            vals.append(v)
        M = []
        for k in range(6):
            sk = sum_up(up(c.hi * nn ** k), 0) + self.tail
            if k == 0:
                M.append(up((1 + 2 * sk) / (2 * np.pi) * (1 + 4 * EPS)))
            else:
                M.append(up(sk / np.pi * (1 + 4 * EPS)))
        inf = dn(vals[0].lo.min() - up(self.wh / 4 * M[1]))
        assert inf > 0
        self._f[m] = dict(val=vals, M=M, inf=inf)
        return self._f[m]

    def box(self, m, k, h):
        """enclosure of g_m^(k) over [x_j - h, x_j + h] for every half-grid point j (first order: value +- h M_{k+1})"""
        F = self.f(m)
        return F["val"][k].widen(up(h * F["M"][k + 1]))


# ---------------------------------------------------------------- one node of the tree flow, certified

def mu(*xs):
    """upper bound of the product of nonnegative floats/arrays"""
    r = xs[0]
    for x in xs[1:]:
        r = up(r * x)
    return r


def ma(*xs):
    """upper bound of the sum of nonnegative floats/arrays"""
    r = xs[0]
    for x in xs[1:]:
        r = up(r + x)
    return r


def u_derivs(Ig):
    """u = 1/g and its derivatives up to 3 (intervals) from intervals Ig = [g, g', g'', g''']"""
    g0, g1, g2, g3 = Ig
    i1 = g0.recip()
    i2 = i1 * i1
    i3 = i2 * i1
    i4 = i2 * i2
    two, three, six = I.exact(2.0), I.exact(3.0), I.exact(6.0)
    u0 = i1
    u1 = -(g1 * i2)
    u2 = two * g1 * g1 * i3 - g2 * i2
    u3 = -(six * g1 * g1 * g1 * i4) + six * g1 * g2 * i3 - g3 * i2
    return [u0, u1, u2, u3]


def box_bounds(P, Q, U):
    """upper bounds of |d_S^a d_y^b rho|, rho = p(y) q(S - y) u(S), from magnitudes P[k] >= |p^(k)|, Q[k] >= |q^(k)|,
    U[k] >= |u^(k)| over a box (Leibniz rule)"""
    B = {}
    B[(2, 0)] = mu(P[0], ma(mu(Q[2], U[0]), mu(2.0, Q[1], U[1]), mu(Q[0], U[2])))
    B[(1, 1)] = ma(mu(P[1], ma(mu(Q[1], U[0]), mu(Q[0], U[1]))), mu(P[0], ma(mu(Q[2], U[0]), mu(Q[1], U[1]))))
    B[(0, 2)] = mu(ma(mu(P[2], Q[0]), mu(2.0, P[1], Q[1]), mu(P[0], Q[2])), U[0])
    B[(3, 0)] = mu(P[0], ma(mu(Q[3], U[0]), mu(3.0, Q[2], U[1]), mu(3.0, Q[1], U[2]), mu(Q[0], U[3])))
    B[(1, 2)] = ma(mu(P[2], ma(mu(Q[1], U[0]), mu(Q[0], U[1]))), mu(2.0, P[1], ma(mu(Q[2], U[0]), mu(Q[1], U[1]))),
                   mu(P[0], ma(mu(Q[3], U[0]), mu(Q[2], U[1]))))
    B[(2, 1)] = ma(mu(P[1], ma(mu(Q[2], U[0]), mu(2.0, Q[1], U[1]), mu(Q[0], U[2]))),
                   mu(P[0], ma(mu(Q[3], U[0]), mu(2.0, Q[2], U[1]), mu(Q[1], U[2]))))
    return B


def node_parts(Md, mA, mB, Ks):
    """Layout [K, q]: S-cell K (centre s_c = (K + 1/2) w), t-cell q (t = S - y, centre t_c = (q + 1/2) w), so the box centre has
    y_c = s_c - t_c = (K - q) w (a grid point) and the box covers y in [y_c - w, y_c + w].
    Returns centre values (intervals) rho_c, dS_c = d_S rho, dy_c = d_y rho; the quadrature data at the y-cell centres
    (layout [K, J]): dS_mid, d2S_mid; and box bounds B_ab (layout [K, q]) of |d_S^a d_y^b rho|."""
    G, wh = Md.G, Md.wh
    FA, FB, Fm = Md.f(mA), Md.f(mB), Md.f(mA + mB)
    j = np.arange(G)
    sl = (slice(None), None)
    yidx = (Ks[:, None] - j[None, :]) % G            # [K, q] -> y grid index K - q ; also [K, J] -> t grid index K - J
    uc = [x[sl] for x in u_derivs([Fm["val"][k][2 * Ks + 1] for k in range(4)])[:3]]
    # centres of the [K, q] boxes: p at y grid points (half index 2(K-q)), q at t-cell centres (2q+1)
    pc = [FA["val"][k][2 * yidx] for k in range(2)]
    qc = [FB["val"][k][2 * j + 1][None, :] for k in range(2)]
    rho_c = pc[0] * qc[0] * uc[0]
    dS_c = pc[0] * (qc[1] * uc[0] + qc[0] * uc[1])
    dy_c = (pc[1] * qc[0] - pc[0] * qc[1]) * uc[0]
    # quadrature points (layout [K, J]): y-cell centres (2J+1), t = s_c - y = (K - J) w (half index 2(K-J))
    pm = FA["val"][0][2 * j + 1][None, :]
    qm = [FB["val"][k][2 * yidx] for k in range(3)]
    dS_mid = pm * (qm[1] * uc[0] + qm[0] * uc[1])
    d2S_mid = pm * (qm[2] * uc[0] + I.exact(2.0) * qm[1] * uc[1] + qm[0] * uc[2])
    # box magnitudes over [K, q] boxes
    P = [Md.box(mA, k, wh)[2 * yidx].mag() for k in range(3)]
    Q = [Md.box(mB, k, wh / 2)[2 * j + 1].mag()[None, :] for k in range(4)]
    U = [x.mag()[sl] for x in u_derivs([Md.box(mA + mB, k, wh / 2)[2 * Ks + 1] for k in range(4)])]
    B = box_bounds(P, Q, U)
    return rho_c, dS_c, dy_c, dS_mid, d2S_mid, B, yidx


def excl_cumsum(x, n):
    """exclusive prefix sums of an interval array along axis 1 (column J holds the sum over J' < J)"""
    cs = icumsum(x, 1)
    z = np.zeros((n, 1))
    return I(np.concatenate([z, cs.lo[:, :-1]], 1), np.concatenate([z, cs.hi[:, :-1]], 1))


def excl_cumsum_up(x, n, G):
    """upper bound of exclusive prefix sums of a nonnegative float array along axis 1"""
    cs = up(np.cumsum(x, 1) * (1 + 2 * G * EPS))
    return np.concatenate([np.zeros((n, 1)), cs[:, :-1]], 1)


def node_cert(Md, mA, cA, mB, HBup, c_choice=None, chunk=64):
    """Certified upper bound h_up[K] >= sup over S-cell K of the expected link cost h(S) of the 1D flow at a node.
    Child A: m_A variables, constant weight cA (its own cost per unit rate, routing included). Child B: m_B variables, with
    h_B(t) <= HBup[q] on t-cell q (t = S - y, the sum of B). Flow velocity of Y_A: a = (G_S(y) + c(S)) / rho_S(y),
    G_S(y) = -int_0^y d_S rho_S; c(S) constant on each S-cell (float choice; every value gives a valid flow).
    Cost: I(S) = cA int |G + c| dy + int hbar(S - y) |rho - G - c| dy, hbar the step function HBup.
    (i) I(s_K) is bounded t-cell by t-cell: int |a + b (t - t_c) + R| dt <= w|a| + [|b| w^2/4 if a may vanish within |b| w/2]
        + w^3/24 sup|F_tt|, with a, b the centre values (point enclosures) and box-local bounds of second derivatives;
    (ii) I(S) <= I(s_K) + (w/2) sup_cell |I'|, |I'| bounded in y- or in t-coordinates (the smaller bound).
    Returns (h_up, L, c_used, h_float): L the bound of |I'|, h_float the float estimate at the box centres."""
    G, w, wh, wI = Md.G, Md.w, Md.wh, Md.wI
    j = np.arange(G)
    h_up, h_Lrec, h_fl, c_used = np.empty(G), np.empty(G), np.empty(G), np.empty(G)
    w2_8 = up(up(wh * wh) / 8)
    w2_4 = up(up(wh * wh) / 4)
    w3_24 = up(up(up(wh * wh) * wh) / 24)
    for K0 in range(0, G, chunk):
        Ks = np.arange(K0, min(G, K0 + chunk))
        n = len(Ks)
        rho_c, dS_c, dy_c, dS_mid, d2S_mid, B, yidx = node_parts(Md, mA, mB, Ks)
        rows = np.arange(n)[:, None]
        # box [K, q] covers y-cells K-q-1 and K-q: for y-cell J use the larger of the boxes q = K-J-1 and q = K-J
        qofJ = (Ks[:, None] - j[None, :] - 1) % G
        B12J = np.maximum(B[(1, 2)][rows, qofJ], B[(1, 2)][rows, (qofJ + 1) % G])
        B21J = np.maximum(B[(2, 1)][rows, qofJ], B[(2, 1)][rows, (qofJ + 1) % G])
        B30J = np.maximum(B[(3, 0)][rows, qofJ], B[(3, 0)][rows, (qofJ + 1) % G])
        # G(s_c, y_J) = -w sum_{J' < J} dS_mid[K, J'] +- sum w^3/24 sup|d_y^2 d_S rho| (midpoint rule), layout [K, J]
        Gcum = (-(excl_cumsum(dS_mid, n) * wI)).widen(excl_cumsum_up(mu(w3_24, B12J), n, G))
        # d_S G(s_c, y_J), crude midpoint error w^2/4 sup|d_y d_S^2 rho| per cell (enters radii only)
        SGcum = (-(excl_cumsum(d2S_mid, n) * wI)).widen(excl_cumsum_up(mu(w2_4, B21J), n, G))
        # sup over a box of |d_S^2 G(S, y)| <= int |d_S^3 rho| over [0, y] or over [y, 2 pi] (int_0^{2pi} d_S^3 rho = 0);
        # the box has y in [y_J - w, y_J + w]: forward sum over cells J' <= J, backward over J' >= J - 1
        a3 = mu(wh, B30J)
        fw = np.cumsum(a3, 1)
        bw = np.cumsum(a3[:, ::-1], 1)[:, ::-1]
        bwm = np.concatenate([bw[:, :1], bw[:, :-1]], 1)
        GssJ = up(np.minimum(fw, bwm) * (1 + 2 * G * EPS) + 1e-300)
        # to layout [K, q]: J = K - q
        G_c = Gcum[rows, yidx]
        SG_c = SGcum[rows, yidx]
        Gss = GssJ[rows, yidx]
        D_c = rho_c - G_c
        HB = HBup[None, :] * np.ones((n, 1))
        Gm, Dm = 0.5 * (G_c.lo + G_c.hi), 0.5 * (D_c.lo + D_c.hi)
        if c_choice is None:
            bp = np.concatenate([-Gm, Dm], axis=1)
            wt = np.concatenate([np.broadcast_to(cA * np.ones(G), Gm.shape), HB], axis=1)
            o = np.argsort(bp, axis=1)
            cw = np.cumsum(np.take_along_axis(wt, o, 1), axis=1)
            pos = np.argmax(cw >= cw[:, -1:] / 2, axis=1)
            c = np.take_along_axis(bp, o, 1)[np.arange(n), pos]
        else:
            c = c_choice[Ks]
        cI = I.exact(c[:, None])
        B20, B11, B02 = B[(2, 0)], B[(1, 1)], B[(0, 2)]
        # I(S) = cA int |G(S,y) + c| dy + sum_q h_q int_{S - y in cell q} |rho - G - c|(S, y) dy.
        # (i) at S = s_c, per t-cell: int |a + b (t - t_c) + R| dt <= w|a| + [|b| w^2/4 if a may vanish within |b| w/2]
        #     + w^3/24 sup|F_tt|, F(t) = f(s_c, s_c - t): a = f at the centre, b = |f_y| at the centre, F_tt = f_yy.
        # (ii) |I'(S)| <= cA int |d_S G| + sum_q h_q int_window |d_S (rho - G)| + sum_q |h_q - h_{q-1}| |f(S, S - q w)|
        #     (the windows move with S; summation by parts), so I(S) <= I(s_c) + (w/2) sup_cell |I'|.

        def cell_int(aI, bmag, ftt):
            amag = aI.mag()
            amig = np.where((aI.lo <= 0) & (aI.hi >= 0), 0.0, np.minimum(np.abs(aI.lo), np.abs(aI.hi)))
            corr = np.where(amig < mu(bmag, wh / 2), mu(bmag, w2_4), 0.0)
            return ma(mu(wh, amag), corr, mu(w3_24, ftt))

        aG = G_c + cI
        aD = D_c - cI
        ciG = cell_int(aG, dS_c.mag(), B11)
        ciD = cell_int(aD, (dy_c + dS_c).mag(), ma(B02, B11))
        # sup over the box (S-cell, y in [y_c - w, y_c + w]) of |d_S G|, |d_S (rho - G)|, |d_y (rho - G)|, |rho - G - c|
        dGS = ma(SG_c.mag(), mu(wh / 2, Gss), mu(wh, B20))
        dDS = ma((dS_c - SG_c).mag(), mu(wh / 2, ma(B20, Gss)), mu(wh, ma(B11, B20)))
        supfy = ma((dy_c + dS_c).mag(), mu(wh / 2, ma(B11, B20)), mu(wh, ma(B02, B11)))
        supD = ma(aD.mag(), mu(wh / 2, dDS), mu(wh, supfy))
        Hc = HBup[None, :]
        jump = up(np.abs(HBup - np.roll(HBup, 1)) * (1 + 2 * EPS))[None, :]   # |h_q - h_{q-1}|
        # (i) I(s_K), t-cell by t-cell ;  (ii) sup over the S-cell of |I'(S)|, the smaller of two bounds:
        # (L1) y-coordinates: d_S f at fixed y, plus the moving windows (summation by parts: jumps of the step bound);
        # (L2) t-coordinates, I(S) = int hbar(t) |f(S, S - t)| dt: derivative d_S f + d_y f.
        val = ma(mu(float(cA), ciG), mu(ciD, Hc))
        lip1 = ma(mu(float(cA), wh, dGS), mu(Hc, wh, dDS), mu(jump, supD))
        sGt = ma((SG_c - dS_c).mag(), mu(wh / 2, ma(Gss, B20)), mu(wh, ma(B20, B11)))
        sDt = ma((dS_c - SG_c + dy_c + dS_c).mag(), mu(wh / 2, ma(B20, Gss, B11, B20)), mu(wh, ma(B11, B20, B02, B11)))
        lip2 = ma(mu(float(cA), wh, sGt), mu(Hc, wh, sDt))
        L = np.minimum(sum_up(lip1, 1), sum_up(lip2, 1))
        h_up[Ks] = up(up(sum_up(val, 1) * (1 + 4 * EPS)) + up(up(L * (1 + 4 * EPS)) * (wh / 2)))
        h_Lrec[Ks] = L
        h_fl[Ks] = w * (cA * np.abs(Gm + c[:, None]) + np.abs(Dm - c[:, None]) * HB).sum(1)
        c_used[Ks] = c
    return h_up, h_Lrec, c_used, h_fl


# ---------------------------------------------------------------- geometry

def rest_costs(l, i):
    """routing costs of the Rest variables for the parallel link at bottom-face position i (followups 2a, PREREG):
    inner plaquette (a, b): |a - i| + b; face link: (distance of its adjacent plaquette) + 1; f_i excluded."""
    out = [abs(a - i) + b for a in range(l) for b in range(l)]
    out += [abs(j - i) + 1 for j in range(l) if j != i]
    out += [abs(j - i) + l - 1 + 1 for j in range(l)]
    out += [i + j + 1 for j in range(l)]
    out += [(l - 1 - i) + j + 1 for j in range(l)]
    return sorted(out, reverse=True)


def kP_cert(Md, l, i, log=True):
    G = Md.G
    costs = rest_costs(l, i)
    assert len(costs) == l * l + 4 * l - 1
    acc_m, acc = 1, np.full(G, float(costs[-1]))
    t0 = time.time()
    for k in range(len(costs) - 2, -1, -1):
        h_up, L, _, h_fl = node_cert(Md, 1, float(costs[k]), acc_m, acc)
        acc_m += 1
        acc = h_up
        if log and (k % 20 == 0):
            print("  node m=%d: h_up max %.5f, L max %.3f (float %.5f) %.0fs" % (acc_m, h_up.max(), L.max(), h_fl.max(),
                                                                              time.time() - t0), flush=True)
    root_up, _, _, root_fl = node_cert(Md, 1, 0.0, acc_m, up(1.0 + acc))
    return root_up, root_fl


def R_upper(kappa):
    """upper bound of R(kappa) = 2 P_kappa(|x| < pi/2) - 1 = (4/pi) sum_k (-1)^k I_{2k+1}(kappa) / ((2k+1) I_0(kappa)),
    an alternating series with decreasing terms: partial sum ending after a negative term + the next (positive) term."""
    k_ = mp.mpf(kappa)
    i0 = mp.besseli(0, k_)
    s = mp.mpf(0)
    for kk in range(0, 400):
        t = mp.besseli(2 * kk + 1, k_) / ((2 * kk + 1) * i0)
        if kk % 2 == 1 and t < mp.mpf(10) ** -35:
            s += t  # bound: S_odd_partial + next positive term
            break
        s += t if kk % 2 == 0 else -t
    return up(float(4 / mp.pi * s * (1 + mp.mpf(10) ** -30)))


def kD_cert(Md, l):
    G, w, wh = Md.G, Md.w, Md.wh
    N = l * l + 4 * l
    # kappa_hi per u-cell: 2 beta max |cos(u/2)| over [J w, (J+1) w] (monotone pieces: max at an endpoint)
    Rup = np.empty(G)
    for J in range(G):
        cmax = max(abs(mp.cos(mp.pi * J / G)), abs(mp.cos(mp.pi * (J + 1) / G)))
        Rup[J] = R_upper(2 * mp.mpf(Md.beta) * cmax * (1 + mp.mpf(10) ** -30))
    # node with A = the pair (2 variables, weight R per y-cell), B = the rest (N - 2), and no flow constant: we only need
    # sup over Phi of int rho_Phi(u) Rup(u) du, rho over boxes = centre +- radius
    FA, FB, Fm = Md.f(2), Md.f(N - 2), Md.f(N)
    j = np.arange(G)
    idx = (j[:, None] - j[None, :]) % G     # [K, J] -> t = s_c - u_c = (K - J) w, half index 2(K - J)
    sl = (slice(None), None)
    uc = [x[sl] for x in u_derivs([Fm["val"][k][2 * j + 1] for k in range(4)])[:2]]
    pc = [FA["val"][k][2 * j + 1][None, :] for k in range(2)]
    qc = [FB["val"][k][2 * idx] for k in range(2)]
    rho_c = pc[0] * qc[0] * uc[0]
    dS_c = pc[0] * (qc[1] * uc[0] + qc[0] * uc[1])
    dy_c = (pc[1] * qc[0] - pc[0] * qc[1]) * uc[0]
    P = [Md.box(2, k, wh / 2)[2 * j + 1].mag()[None, :] for k in range(3)]
    Q = [Md.box(N - 2, k, wh)[2 * idx].mag() for k in range(4)]
    U = [x.mag()[sl] for x in u_derivs([Md.box(N, k, wh / 2)[2 * j + 1] for k in range(4)])]
    Bd = box_bounds(P, Q, U)
    # rho over the box (S-cell x u-cell) <= centre + (w/2)(|rho_S| + |rho_u|) + (w^2/8)(B20 + 2 B11 + B02)
    r = ma(mu(wh / 2, ma(dS_c.mag(), dy_c.mag())), mu(up(up(wh * wh) / 8), ma(Bd[(2, 0)], mu(2.0, Bd[(1, 1)]), Bd[(0, 2)])))
    rho_hi = up(rho_c.hi + r)
    out = up(3 * sum_up(up(rho_hi * Rup[None, :]), 1) * wh * (1 + 4 * EPS))
    fl = 3 * w * (0.5 * (rho_c.lo + rho_c.hi) * Rup[None, :]).sum(1)
    return out, fl


# ---------------------------------------------------------------- main

def store(beta, l, key, val):
    path = os.path.join(HERE, "cert_%g_%d.json" % (beta, l))
    res = json.load(open(path)) if os.path.exists(path) else {}
    res[key] = val
    json.dump(res, open(path, "w"), indent=1)


def main():
    mode = sys.argv[1]
    if mode == "P":
        beta, l, i, G = float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
        t0 = time.time()
        Md = Model(beta, G)
        up_, fl = kP_cert(Md, l, i)
        val = dict(k_up=float(up_.max()), k_float=float(fl.max()), argmax_cell=int(up_.argmax()),
                   k_up_min_over_phi=float(up_.min()), G=G, secs=time.time() - t0)
        print("beta=%g l=%d i=%d G=%d: certified kP <= %.6f (float %.6f) %.0fs" % (beta, l, i, G, val["k_up"],
                                                                                   val["k_float"], val["secs"]))
        store(beta, l, "P%d" % i, val)
    elif mode == "D":
        beta, l, G = float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        t0 = time.time()
        Md = Model(beta, G)
        up_, fl = kD_cert(Md, l)
        val = dict(k_up=float(up_.max()), k_float=float(fl.max()), G=G, secs=time.time() - t0)
        print("beta=%g l=%d G=%d: certified kD <= %.6f (float %.6f) %.0fs" % (beta, l, G, val["k_up"], val["k_float"],
                                                                              val["secs"]))
        store(beta, l, "D", val)
    elif mode == "gamma":
        beta, l = float(sys.argv[2]), int(sys.argv[3])
        res = json.load(open(os.path.join(HERE, "cert_%g_%d.json" % (beta, l))))
        kp = [res["P%d" % min(i, l - 1 - i)]["k_up"] for i in range(l)]
        kd = res["D"]["k_up"]
        num = mp.mpf(0)
        for v in kp:
            num += 2 * mp.mpf(v)
        num += 2 * (l - 1) * mp.mpf(kd) + 4 * mp.mpf(kp[0])
        gam = num / (l * (l + 1))  # exact rational arithmetic on the float bounds (mpmath, 40 digits)
        print("beta=%g l=%d: certified gamma <= %s" % (beta, l, mp.nstr(gam, 12)))
        store(beta, l, "gamma", dict(gamma_up=float(up(float(gam))), kP=kp, kD=kd))


if __name__ == "__main__":
    main()
