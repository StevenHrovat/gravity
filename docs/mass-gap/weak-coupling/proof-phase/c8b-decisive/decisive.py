"""c8b-decisive: the two tools of the decisive one-box test (cycle 8, workstream 2).

  couple  : upper bound for kappa(u) of the Lean one-box criterion (c7c-onebox/NOTE.md section 3.4): two heat-bath chains for the box
            under two boundary conditions that differ in ONE outside cell, coupled link by link with the MAXIMAL coupling of the two
            single-link (staple) laws, in a running gauge alignment of chain 2 to chain 1; the number of disagreeing box cells
            (coarse links) at stationarity is an upper bound of kappa(u) in expectation.  Groups su2 and u1.
  tie     : the tie test (section 5 of the NOTE, mechanism (T)): two vortex-sheet arrangements (flat sheets / tube) that are degenerate,
            a one-cell breaker that changes their free-energy difference by O(1), and a sampler that sees both: runs started from both
            arrangements, thermodynamic integration of the breaker in each (ratio method), direct occupation when the chain mixes.
            Groups su2, z2, i2 (binary icosahedral).
  analyse / selftest / pilot : see below.

Reuses lattice/boundary.py unchanged (Box, boundary conditions, staples, gauge tools).  Nothing outside this folder is modified.
"""

import argparse
import glob
import json
import math
import os
import subprocess
import sys
import time

sys.dont_write_bytecode = True
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
LAT = os.path.normpath(os.path.join(HERE, "..", "..", "..", "lattice"))
sys.path.insert(0, LAT)
import boundary as bd  # noqa: E402

TOL = 1e-7  # two links agree if their distance is below this (agreement is exact bit equality after a maximal-coupling success)


# ====================================================================================================================== random numbers

class RNG:
    def __init__(self, xp, seed):
        self.xp = xp
        self.g = np.random.default_rng(seed) if xp is np else xp.random.RandomState(seed)

    def uniform(self, shape):
        return self.g.random(shape) if self.xp is np else self.g.random_sample(shape)

    def normal(self, shape):
        return self.g.standard_normal(shape)


def su2_x0(xp, alpha, rng):
    """x0 with density sqrt(1 - x0^2) exp(alpha x0): Kennedy-Pendleton for alpha >= 0.3, direct rejection below (as boundary.kp_x0),
    array code for numpy or cupy."""
    a_all = xp.maximum(alpha, 1e-12)
    out = xp.zeros(alpha.shape)
    pend = xp.arange(alpha.size)
    while pend.size:
        a = a_all[pend]
        u = rng.uniform((4, int(pend.size)))
        r1, r2, r3, r4 = 1.0 - u[0], u[1], 1.0 - u[2], u[3]
        lam2 = -(xp.log(r1) + xp.cos(2 * np.pi * r2) ** 2 * xp.log(r3)) / (2 * a)
        xs = 2.0 * r2 - 1.0
        small = a < 0.3
        val = xp.where(small, xs, 1.0 - 2.0 * lam2)
        ok = xp.where(small, r4 <= xp.sqrt(xp.maximum(1.0 - xs * xs, 0.0)) * xp.exp(a * (xs - 1.0)), r4 * r4 <= 1.0 - lam2)
        out[pend[ok]] = val[ok]
        pend = pend[~ok]
    return out


def vonmises_s(xp, kappa, rng):
    """Angle with density exp(kappa cos t), Best-Fisher, array code."""
    k_all = xp.maximum(kappa, 1e-6)
    tau = 1.0 + xp.sqrt(1.0 + 4.0 * k_all * k_all)
    rho = (tau - xp.sqrt(2.0 * tau)) / (2.0 * k_all)
    r_all = (1.0 + rho * rho) / (2.0 * rho)
    out = xp.zeros(kappa.shape)
    pend = xp.arange(kappa.size)
    while pend.size:
        k, r = k_all[pend], r_all[pend]
        u = rng.uniform((3, int(pend.size)))
        z = xp.cos(np.pi * u[0])
        f = (1.0 + r * z) / (r + z)
        c = k * (r - f)
        u2 = xp.maximum(u[1], 1e-300)
        ok = (c * (2.0 - c) - u2 > 0) | (xp.log(xp.maximum(c, 1e-300) / u2) + 1.0 - c >= 0)
        val = xp.sign(u[2] - 0.5) * xp.arccos(xp.clip(f, -1.0, 1.0))
        tiny = kappa[pend] < 1e-6
        val = xp.where(tiny, np.pi * (2.0 * u[2] - 1.0), val)
        ok = ok | tiny
        out[pend[ok]] = val[ok]
        pend = pend[~ok]
    return out


_M = 64
_TH_S = np.arange(1, _M) * np.pi / _M          # SU(2): integral over theta in (0, pi) of exp(k (cos theta - 1)) sin^2 theta
_TH_U = np.arange(_M) * 2 * np.pi / _M          # U(1): mean over the circle of exp(k (cos theta - 1))


def lz_su2(xp, kappa):
    """ln Z(kappa) up to a constant that cancels in ratios: kappa + ln mean_j exp(kappa (cos th_j - 1)) sin^2 th_j (trapezoid rule of a
    periodic analytic integrand: exact to rounding for kappa < 30).  Z = I_1(kappa)/kappa up to a constant."""
    th = xp.asarray(_TH_S)
    return kappa + xp.log((xp.exp(kappa[..., None] * (xp.cos(th) - 1.0)) * xp.sin(th) ** 2).sum(axis=-1) / _M)


def lz_u1(xp, kappa):
    th = xp.asarray(_TH_U)
    return kappa + xp.log(xp.exp(kappa[..., None] * (xp.cos(th) - 1.0)).sum(axis=-1) / _M)


# ====================================================================================================================== single-link laws

class Law:
    """Single-link heat-bath law  p(U) ~ exp(beta Re(U A))  for the staple sum A (quaternion (n, 4) for SU(2), complex (n,) for U(1))."""

    def __init__(self, group, beta, xp, rng):
        self.group, self.beta, self.xp, self.rng = group, beta, xp, rng

    def knorm(self, A):
        return self.xp.linalg.norm(A, axis=-1) if self.group == "su2" else self.xp.abs(A)

    def lz(self, A):
        k = self.beta * self.knorm(A)
        return lz_su2(self.xp, k) if self.group == "su2" else lz_u1(self.xp, k)

    def expo(self, U, A):
        """beta Re(U A): quaternion product real part / Re(A e^{i theta})."""
        if self.group == "su2":
            return self.beta * (U[..., 0] * A[..., 0] - (U[..., 1:] * A[..., 1:]).sum(axis=-1))
        return self.beta * (A * self.xp.exp(1j * U)).real

    def sample(self, A):
        xp, rng = self.xp, self.rng
        if self.group == "su2":
            k = xp.linalg.norm(A, axis=-1)
            Ah = A / xp.maximum(k, 1e-300)[..., None]
            x0 = su2_x0(xp, self.beta * k, rng)
            v = xp.asarray(rng.normal(k.shape + (3,)))
            v = v / xp.linalg.norm(v, axis=-1, keepdims=True)
            X = xp.concatenate([x0[..., None], v * xp.sqrt(xp.maximum(0.0, 1.0 - x0 * x0))[..., None]], axis=-1)
            return bd.qmul(X, Ah * xp.asarray([1.0, -1.0, -1.0, -1.0]), xp)
        vm = vonmises_s(xp, self.beta * xp.abs(A), rng)
        return xp.angle(xp.exp(1j * (-xp.angle(A) + vm)))

    def coupled(self, A1, A2):
        """Maximal coupling of the laws for the staples A1 and A2 (flat arrays): returns (U1, U2), U1 ~ p(.|A1), U2 ~ p(.|A2), and
        U1 = U2 with the largest possible probability 1 - TV.  U1 ~ p1; accepted (U2 = U1) with probability min(1, p2/p1); otherwise U2 is
        drawn from the residual (p2 - p1)_+ by rejection from p2 with acceptance (1 - p1/p2)_+ / a_max, a_max the supremum of that
        function (so the acceptance probability stays of order one even when the two laws almost agree)."""
        xp, rng = self.xp, self.rng
        n = A1.shape[0]
        U1 = self.sample(A1)
        c = self.lz(A1) - self.lz(A2)                                     # ln Z1 - ln Z2
        L = self.expo(U1, A2) - self.expo(U1, A1) + c                       # ln p2/p1 at U1
        w = rng.uniform((n,))
        acc = xp.log(xp.maximum(w, 1e-300)) <= L
        U2 = U1.copy()
        pend = xp.nonzero(~acc)[0]
        if pend.size == 0:
            return U1, U2
        D = A2[pend] - A1[pend]
        Lmax = self.beta * self.knorm(D) + c[pend]
        amax = xp.maximum(1.0 - xp.exp(-Lmax), 1e-300)
        cc = c[pend]
        a1, a2 = A1[pend], A2[pend]
        out = xp.zeros((pend.size,) + U1.shape[1:])
        loc = xp.arange(pend.size)
        for it in range(200000):
            V = self.sample(a2[loc])
            Lv = self.expo(V, a2[loc]) - self.expo(V, a1[loc]) + cc[loc]
            a = xp.maximum(1.0 - xp.exp(-Lv), 0.0)
            ok = rng.uniform((int(loc.size),)) * amax[loc] <= a
            out[loc[ok]] = V[ok]
            loc = loc[~ok]
            if loc.size == 0:
                break
        else:
            raise RuntimeError("residual sampler did not converge")
        U2[pend] = out
        return U1, U2


# ====================================================================================================================== geometry

def block_of(ell, nc):
    """Cell index of a site coordinate 0..ell: nc cells of equal size ell / nc along each axis (the last one takes the far face)."""
    return np.minimum(np.arange(ell + 1) * nc // ell, nc - 1)


def site_blocks(box, nc):
    """(4, N^4) cell coordinates of the sites of the embedding lattice (coordinates > ell are clipped to the last cell, never used)."""
    N, ell = box.N, box.ell
    b = np.concatenate([block_of(ell, nc), np.full(N - ell - 1, nc - 1)]) if N > ell + 1 else block_of(ell, nc)
    idx = np.indices(box.dims)
    return np.stack([b[idx[i]].reshape(-1) for i in range(4)])


def class_reps(nc, cap=0):
    """Symmetry classes of the cells of one face (a 3D grid of nc^3 cells): sorted depth triples; returns [(pos, multiplicity)] with pos
    the representative cell (y, z, t) of the face x = 0.  cap > 0: depths above cap are merged (an approximation, valid when the influence
    of a cell does not reach further than cap cells: used only in the strong-coupling anchors, where D(r) = 0 beyond r = 1)."""
    d = [min(i, nc - 1 - i) for i in range(nc)]
    if cap:
        d = [min(x, cap) for x in d]
    cls = {}
    for i in range(nc):
        for j in range(nc):
            for k in range(nc):
                key = tuple(sorted((d[i], d[j], d[k])))
                cls[key] = cls.get(key, 0) + 1
    return [(key, m) for key, m in sorted(cls.items())]


def patch_range(ell, nc, q):
    s = np.arange(ell + 1)
    return s[block_of(ell, nc) == q]


def inbox_links(box):
    """(4, N^4) bool: link (s, mu) lies in the box (all coordinates 0..ell, s_mu <= ell - 1)."""
    ell = box.ell
    idx = np.indices(box.dims)
    inb = (idx <= ell).all(axis=0)
    return [(inb & (idx[mu] <= ell - 1)).reshape(-1) for mu in range(4)]


# ====================================================================================================================== boundary changes

def perturb(group, W, box, nc, pos, mode, seed):
    """Change ONE outside cell (a patch of the face x = 0: the tangential links of the sites of the cell pos = (y, z, t) of the 3D face
    grid) in chain 2.  W: list of 4 host arrays (B, N, N, N, N[, 4]) ; pos: (B, 3) cell coordinates.
    flip : the centre element (SU(2) times -1, U(1) angle + pi)
    rand : fresh Haar random links
    gauge: pure-gauge change, a random gauge transformation g at the sites of the cell applied to every link of the box touching them
    none : nothing.   Returns the list of boolean site masks (B, N^4) of the changed sites (for the gauge mode, else empty)."""
    B = W[0].shape[0]
    ell = box.ell
    rng = np.random.default_rng(555 + seed)
    changed = np.zeros((B, box.N ** 4), bool)
    if mode == "none":
        return changed
    G = None
    if mode == "gauge":
        if group == "su2":
            G = np.zeros((B,) + box.dims + (4,))
            G[..., 0] = 1.0
        else:
            G = np.zeros((B,) + box.dims)
    for b in range(B):
        ry, rz, rt = (patch_range(ell, nc, int(q)) for q in pos[b])
        if mode == "gauge":
            ix = np.ix_([0], ry, rz, rt)
            shape = (len(ry), len(rz), len(rt))
            if group == "su2":
                r = rng.normal(size=(1,) + shape + (4,))
                r /= np.linalg.norm(r, axis=-1, keepdims=True)
                G[(b,) + ix] = r
            else:
                G[(b,) + ix] = rng.uniform(-np.pi, np.pi, size=(1,) + shape)
            m = np.zeros(box.dims, bool)
            m[ix] = True
            changed[b] = m.reshape(-1)
            continue
        for mu in (1, 2, 3):
            rr = [np.array([0]), ry, rz, rt]
            rr[mu] = rr[mu][rr[mu] <= ell - 1]
            ix = np.ix_(*rr)
            shape = tuple(len(x) for x in rr)
            if mode == "flip":
                if group == "su2":
                    W[mu][(b,) + ix] = -W[mu][(b,) + ix]
                else:
                    W[mu][(b,) + ix] = np.angle(np.exp(1j * (W[mu][(b,) + ix] + np.pi)))
            else:
                if group == "su2":
                    r = rng.normal(size=shape + (4,))
                    W[mu][(b,) + ix] = r / np.linalg.norm(r, axis=-1, keepdims=True)
                else:
                    W[mu][(b,) + ix] = rng.uniform(-np.pi, np.pi, size=shape)
    if mode == "gauge":
        ops = bd.make_ops(group, np)
        V = bd.gauge_transform(ops, W, G)
        for mu in range(4):
            W[mu][...] = V[mu]
    return changed


# ====================================================================================================================== gauge alignment

class HamAligner:
    """Running gauge alignment of chain 2 to chain 1 (NOTE section 3.4: the labels h_x may be re-chosen at any time as a function of the
    running pair; chain 2 is only RELABELLED, its law is untouched).  At every free site the label is replaced by the one among the
    identity and the 8 rotations that make one incident link agree exactly, that gives the largest number of agreeing links (Hamming
    optimum; a Landau-type sum of distances would rotate agreeing links by small angles and inflate the count).  Checkerboard passes
    (the 8 links of a site are not shared with a site of equal parity), sparse: only sites with a disagreeing incident link."""

    def __init__(self, ops, box, B, free, xp, tol=TOL):
        self.ops, self.xp, self.tol, self.B = ops, xp, tol, B
        N = box.N
        ns = N ** 4
        self.ns = ns
        idx = np.arange(ns).reshape(box.dims)
        self.nbm = [xp.asarray(np.roll(idx, 1, axis=mu).reshape(-1)) for mu in range(4)]
        self.inb = [xp.asarray(m) for m in inbox_links(box)]
        par = np.indices(box.dims).sum(axis=0).reshape(-1) % 2
        self.par = [xp.asarray(par == 0), xp.asarray(par == 1)]
        self.free = xp.asarray(free)
        self.extra = (4,) if ops.group == "su2" else ()

    def mism(self, U, W):
        o = self.ops
        out = []
        for mu in range(4):
            d = bd.link_dist(o, U[mu], W[mu]).reshape(self.B, self.ns)
            out.append((d > self.tol) & self.inb[mu][None, :])
        return out

    def __call__(self, U, W, max_pass=8):
        o, xp = self.ops, self.xp
        B, ns = self.B, self.ns
        nchg = 0
        for _ in range(max_pass):
            moved = 0
            for p in (0, 1):
                M = self.mism(U, W)
                cnt = 0
                for mu in range(4):
                    cnt = cnt + M[mu].astype(np.int8) + M[mu][:, self.nbm[mu]].astype(np.int8)
                sel = self.free & (cnt > 0) & self.par[p][None, :]
                bi, si = xp.nonzero(sel)
                if bi.size == 0:
                    continue
                Uf = [u.reshape((B, ns) + self.extra) for u in U]
                Wf = [w.reshape((B, ns) + self.extra) for w in W]
                Uo, Wo, Ui, Wi, ino, ini = [], [], [], [], [], []
                for mu in range(4):
                    sm = self.nbm[mu][si]
                    Uo.append(Uf[mu][bi, si]); Wo.append(Wf[mu][bi, si])
                    Ui.append(Uf[mu][bi, sm]); Wi.append(Wf[mu][bi, sm])
                    ino.append(self.inb[mu][si]); ini.append(self.inb[mu][sm])
                one = xp.zeros_like(Uo[0])
                if o.group == "su2":
                    one[..., 0] = 1.0
                cands = [one] + [o.mul(Uo[mu], o.dag(Wo[mu])) for mu in range(4)] + [o.mul(o.dag(Ui[mu]), Wi[mu]) for mu in range(4)]
                score = []
                for g in cands:
                    s = 0
                    for mu in range(4):
                        s = s + (bd.link_dist(o, o.mul(g, Wo[mu]), Uo[mu]) <= self.tol) * ino[mu] \
                              + (bd.link_dist(o, o.mul(Wi[mu], o.dag(g)), Ui[mu]) <= self.tol) * ini[mu]
                    score.append(s)
                score = xp.stack(score)                    # (9, n)
                best = xp.argmax(score, axis=0)
                better = score[best, xp.arange(best.size)] > score[0]
                if not bool(better.any()):
                    continue
                G = xp.stack(cands)[best, xp.arange(best.size)]   # (n, ...)
                bsel, ssel, Gs = bi[better], si[better], G[better]
                for mu in range(4):
                    smm = self.nbm[mu][ssel]
                    m1 = self.inb[mu][ssel]
                    new = o.mul(Gs, Wf[mu][bsel, ssel])
                    cur = Wf[mu][bsel, ssel]
                    Wf[mu][bsel, ssel] = xp.where(m1.reshape((-1,) + (1,) * len(self.extra)), new, cur)
                    m2 = self.inb[mu][smm]
                    new = o.mul(Wf[mu][bsel, smm], o.dag(Gs))
                    cur = Wf[mu][bsel, smm]
                    Wf[mu][bsel, smm] = xp.where(m2.reshape((-1,) + (1,) * len(self.extra)), new, cur)
                moved += int(bsel.size)
            nchg += moved
            if moved == 0:
                break
        return nchg


# ====================================================================================================================== coupled chains

class CoupledChains:
    def __init__(self, group, box, beta, U, W, seed, xp, free, n_or=0, align="ham", nc=3, pos=None, kernel="hb", kp=40.0, n_hit=1):
        self.group, self.box, self.beta, self.xp, self.n_or, self.align = group, box, beta, xp, n_or, align
        self.kernel, self.kp, self.n_hit = kernel, kp, n_hit
        self.ops = bd.make_ops(group, xp)
        self.U = [xp.array(u, dtype=float) for u in U]
        self.W = [xp.array(w, dtype=float) for w in W]
        self.B = self.U[0].shape[0]
        self.rng = RNG(xp, seed)
        self.law = Law(group, beta, xp, self.rng)
        self.lawp = Law(group, 1.0, xp, self.rng)      # proposal law (concentration kp around the current link): beta = 1, A = kp * dag(link)
        self.masks = [[xp.asarray(box.dyn[mu] & box.parity[p]) for p in (0, 1)] for mu in range(4)]
        self.dyn = [xp.asarray(d) for d in box.dyn]
        # sparse staples: gather tables for the sites of every (mu, parity) set
        ns = box.N ** 4
        grid = np.arange(ns).reshape(box.dims)
        self.ns = ns
        self.sidx = [[None, None] for _ in range(4)]
        self.stab = [[None, None] for _ in range(4)]
        for mu in range(4):
            for p in (0, 1):
                x = np.nonzero((box.dyn[mu] & box.parity[p]).reshape(-1))[0]
                self.sidx[mu][p] = xp.asarray(x)
                tabs = []
                for nu in range(4):
                    if nu == mu:
                        continue
                    pm = np.roll(grid, -1, axis=mu).reshape(-1)       # x + mu
                    pn = np.roll(grid, -1, axis=nu).reshape(-1)       # x + nu
                    mn = np.roll(grid, 1, axis=nu).reshape(-1)        # x - nu
                    pmmn = np.roll(np.roll(grid, -1, axis=mu), 1, axis=nu).reshape(-1)   # x + mu - nu
                    tabs.append((nu, xp.asarray(pm[x]), xp.asarray(pn[x]), xp.asarray(mn[x]), xp.asarray(pmmn[x])))
                self.stab[mu][p] = tabs
        self.aligner = HamAligner(self.ops, box, self.B, free, xp) if align == "ham" else None
        # cells
        blk = site_blocks(box, nc)
        self.nc = nc
        cellflat = ((blk[0] * nc + blk[1]) * nc + blk[2]) * nc + blk[3]          # (N^4,)
        self.ncell1 = nc ** 4
        self.cell_id = [xp.asarray(mu * self.ncell1 + cellflat) for mu in range(4)]
        self.dynflat = [xp.asarray(box.dyn[mu].reshape(-1)) for mu in range(4)]
        pos = np.zeros((self.B, 3), int) if pos is None else pos
        cb = np.indices((nc,) * 4).reshape(4, -1)                                  # cell coordinates (c0,c1,c2,c3), flat order as cellflat
        r = np.maximum(np.maximum(np.broadcast_to(cb[0][None, :], (self.B, cb.shape[1])), np.abs(cb[1][None, :] - pos[:, 0:1])),
                       np.maximum(np.abs(cb[2][None, :] - pos[:, 1:2]), np.abs(cb[3][None, :] - pos[:, 2:3])))  # (B, nc^4)
        self.rcell = xp.asarray(np.tile(r, (1, 4)))                              # (B, 4 nc^4)
        self.c0cell = xp.asarray(np.tile(cb[0][None, :], (self.B, 4)))

    def staple(self, C, mu):
        return bd.staple_generic(self.ops, C, mu)

    def staple_s(self, C, mu, p):
        """Staple sum A of the links (mu, parity p) of the dynamic set only, by gathering: (B, n, 4) quaternions (SU(2)) or (B, n) complex
        (U(1)); the same as staple_generic(...)[:, mask] (checked in the selftest)."""
        xp, o = self.xp, self.ops
        B, ns = self.B, self.ns
        x = self.sidx[mu][p]
        if self.group == "su2":
            Cf = [c.reshape(B, ns, 4) for c in C]
            A = 0
            for nu, a, b, c_, d in self.stab[mu][p]:
                A = A + o.mul(o.mul(Cf[nu][:, a], o.dag(Cf[mu][:, b])), o.dag(Cf[nu][:, x]))                       + o.mul(o.mul(o.dag(Cf[nu][:, d]), o.dag(Cf[mu][:, c_])), Cf[nu][:, c_])
            return A
        Cf = [c.reshape(B, ns) for c in C]
        A = 0
        for nu, a, b, c_, d in self.stab[mu][p]:
            A = A + xp.exp(1j * (Cf[nu][:, a] - Cf[mu][:, b] - Cf[nu][:, x])) + xp.exp(1j * (-Cf[nu][:, d] - Cf[mu][:, c_] + Cf[nu][:, c_]))
        return A

    def _proposal_axis(self, link):
        """staple-like argument A with Re(V A) = kp <V, link>: kp * conj(link)."""
        if self.group == "su2":
            return self.kp * link * self.xp.asarray([1.0, -1.0, -1.0, -1.0])
        return self.kp * self.xp.exp(-1j * link)

    def sweep(self):
        xp, law = self.xp, self.law
        for mu in range(4):
            for p in (0, 1):
                m = self.masks[mu][p]
                if not bool(m.any()):
                    continue
                if self.kernel == "hb":
                    A1 = self.staple_s(self.U, mu, p)
                    A2 = self.staple_s(self.W, mu, p)
                    sh_ = A1.shape
                    f1 = A1.reshape((-1,) + sh_[2:])
                    f2 = A2.reshape((-1,) + sh_[2:])
                    u1, u2 = law.coupled(f1, f2)
                    self.U[mu][:, m] = u1.reshape(sh_[:2] + u1.shape[1:])
                    self.W[mu][:, m] = u2.reshape(sh_[:2] + u2.shape[1:])
                    continue
                for _ in range(self.n_hit):          # coupled Metropolis: maximal coupling of the two vMF proposals, common uniform
                    A1 = self.staple_s(self.U, mu, p)
                    A2 = self.staple_s(self.W, mu, p)
                    sh_ = A1.shape
                    f1 = A1.reshape((-1,) + sh_[2:])
                    f2 = A2.reshape((-1,) + sh_[2:])
                    cu = self.U[mu][:, m].reshape((-1,) + (self.U[mu].shape[5:] if self.group == "su2" else ()))
                    cw = self.W[mu][:, m].reshape(cu.shape)
                    v1, v2 = self.lawp.coupled(self._proposal_axis(cu), self._proposal_axis(cw))
                    lr = xp.log(xp.maximum(self.rng.uniform((cu.shape[0],)), 1e-300))
                    a1 = lr < (law.expo(v1, f1) - law.expo(cu, f1))
                    a2 = lr < (law.expo(v2, f2) - law.expo(cw, f2))
                    sel = (slice(None),) + (None,) * (cu.ndim - 1)
                    n1 = xp.where(a1[sel], v1, cu)
                    n2 = xp.where(a2[sel], v2, cw)
                    self.U[mu][:, m] = n1.reshape(sh_[:2] + n1.shape[1:])
                    self.W[mu][:, m] = n2.reshape(sh_[:2] + n2.shape[1:])
        for _ in range(self.n_or):
            for C in (self.U, self.W):
                self.overrelax(C)
        if self.group == "su2":
            for C in (self.U, self.W):
                for mu in range(4):
                    d = self.dyn[mu]
                    C[mu][:, d] /= xp.linalg.norm(C[mu][:, d], axis=-1, keepdims=True)
        if self.aligner is not None:
            return self.aligner(self.U, self.W)
        return 0

    def thermalise(self, n, n_or=3):
        """Chain 1 alone: exact heat bath + overrelaxation with the sparse staples (the fast sampler, used before the coupled run)."""
        xp, law = self.xp, self.law
        for _ in range(n):
            for mu in range(4):
                for p in (0, 1):
                    A = self.staple_s(self.U, mu, p)
                    sh_ = A.shape
                    u = law.sample(A.reshape((-1,) + sh_[2:]))
                    self.U[mu][:, self.masks[mu][p]] = u.reshape(sh_[:2] + u.shape[1:])
            for _ in range(n_or):
                self.overrelax(self.U)
            if self.group == "su2":
                for mu in range(4):
                    d = self.dyn[mu]
                    self.U[mu][:, d] /= xp.linalg.norm(self.U[mu][:, d], axis=-1, keepdims=True)

    def overrelax(self, C):
        xp, o = self.xp, self.ops
        for mu in range(4):
            for p in (0, 1):
                m = self.masks[mu][p]
                if not bool(m.any()):
                    continue
                A = self.staple_s(C, mu, p)
                if self.group == "su2":
                    Ad = o.dag(A / xp.maximum(xp.linalg.norm(A, axis=-1), 1e-300)[..., None])
                    C[mu][:, m] = bd.qmul(bd.qmul(Ad, o.dag(C[mu][:, m]), xp), Ad, xp)
                else:
                    phi = xp.angle(A)
                    C[mu][:, m] = xp.angle(xp.exp(1j * (-2 * phi - C[mu][:, m])))

    def measure(self):
        """D (number of disagreeing cells), D by L-infinity cell distance r from the changed cell, D by depth c0, link disagreement
        fraction, raw plaquette of chain 1 (equilibrium monitor)."""
        xp, o = self.xp, self.ops
        B, nc = self.B, self.nc
        tot = self.ncell1 * 4
        idx_all, nlink, nmis = [], 0, 0
        cellany = xp.zeros(B * tot)
        for mu in range(4):
            d = bd.link_dist(o, self.U[mu], self.W[mu]).reshape(B, -1)
            mis = (d > TOL) & self.dynflat[mu][None, :]
            nmis = nmis + mis.sum(axis=1)
            nlink += int(self.dynflat[mu].sum())
            bi, si = xp.nonzero(mis)
            if bi.size:
                cellany[bi * tot + self.cell_id[mu][si]] = 1.0
        cellany = cellany.reshape(B, tot)
        D = cellany.sum(axis=1)
        Dr = xp.stack([(cellany * (self.rcell == r)).sum(axis=1) for r in range(nc)], axis=1)
        Dc = xp.stack([(cellany * (self.c0cell == r)).sum(axis=1) for r in range(nc)], axis=1)
        return {"D": bd.to_host(D), "Dr": bd.to_host(Dr), "Dc": bd.to_host(Dc), "frac": bd.to_host(nmis) / nlink}

    def plaq(self):
        xp, o = self.xp, self.ops
        P = o.re(o.mul(o.mul(self.U[0], bd.sh(self.U[1], 0)), o.mul(o.dag(bd.sh(self.U[0], 1)), o.dag(self.U[1]))))
        m = xp.asarray(self.box.interior)
        return bd.to_host(P[:, m].mean(axis=1))


def make_bc(group, box, bg, B, seed, beta, gpu, periodic_therm, n_or_per=3):
    """Initial links of chain 1 (host arrays); the frozen links are the boundary condition.  'typical': cut from a periodic equilibrium."""
    U = bd.initial_links(group, box, bg, B, seed)
    if bg == "typical":
        upd = bd.make_updater(group, box, beta, U, seed, gpu)
        upd.set_dynamic([np.ones(box.dims, bool)] * 4)
        for _ in range(periodic_therm):
            upd.sweep(n_or_per)
        U = [bd.to_host(u).copy() for u in upd.links()]
    return U


def couple_run(a):
    gpu = not a.cpu
    xp = bd.get_xp(gpu)
    box = bd.Box(a.ell)
    nc = a.ncell
    cls = class_reps(nc, a.depth_cap)
    if a.positions == "centre":
        cls = [(max(cls, key=lambda c: c[0]), 1)]
    elif a.positions == "corner":
        cls = [(min(cls, key=lambda c: c[0]), 1)]
    reps = [c[0] for c in cls]
    B = len(reps) * a.chains
    pos = np.array([reps[b // a.chains] for b in range(B)])
    t0 = time.time()
    U = make_bc(a.group, box, a.bg, B, a.seed, a.beta, gpu, a.periodic_therm)
    if a.init == "hot":    # chain 1 interior random
        rng = np.random.default_rng(99 + a.seed)
        for mu in range(4):
            if a.group == "su2":
                r = rng.normal(size=U[mu].shape)
                r /= np.linalg.norm(r, axis=-1, keepdims=True)
                U[mu] = np.where(box.dyn[mu][None, ..., None], r, U[mu])
            else:
                U[mu] = np.where(box.dyn[mu][None], rng.uniform(-np.pi, np.pi, U[mu].shape), U[mu])
    if a.pre > 0 and a.init in ("same", "rot"):   # thermalise chain 1 alone with the fast sampler, boundary sigma, before the coupled run
        free0 = np.tile(box.interior.reshape(1, -1), (B, 1))
        s0 = CoupledChains(a.group, box, a.beta, U, U, a.seed + 3, xp, free0, align="none", nc=nc, pos=pos)
        s0.thermalise(a.pre)
        U = [bd.to_host(u).copy() for u in s0.U]
        del s0
    W = [u.copy() for u in U]
    changed = perturb(a.group, W, box, nc, pos, a.pert, a.seed)
    if a.init == "indep":    # chain 2 interior independent random
        rng = np.random.default_rng(1234 + a.seed)
        for mu in range(4):
            if a.group == "su2":
                r = rng.normal(size=W[mu].shape)
                r /= np.linalg.norm(r, axis=-1, keepdims=True)
                W[mu] = np.where(box.dyn[mu][None, ..., None], r, W[mu])
            else:
                W[mu] = np.where(box.dyn[mu][None], rng.uniform(-np.pi, np.pi, W[mu].shape), W[mu])
    if a.init == "rot":      # chain 2 = random interior gauge copy of chain 1 (identical boundary)
        ops = bd.make_ops(a.group, np)
        g = bd.random_gauge(a.group, box, B, np.random.default_rng(4321 + a.seed))
        V = bd.gauge_transform(ops, W, g)
        W = [np.where(box.dyn[mu].reshape((1,) + box.dims + ((1,) if a.group == "su2" else ())), V[mu], W[mu]) for mu in range(4)]
    free = np.tile(box.interior.reshape(1, -1), (B, 1))
    if a.pert == "gauge" and a.boundary_labels:
        free = free | changed
    sim = CoupledChains(a.group, box, a.beta, U, W, a.seed + 7, xp, free, n_or=a.n_or, align=a.align, nc=nc, pos=pos,
                          kernel=a.kernel, kp=a.kp, n_hit=a.n_hit)
    rec = {}
    series = []

    def save(m, partial):
        np.savez(a.out, group=a.group, beta=a.beta, ell=a.ell, ncell=nc, bg=a.bg, pert=a.pert, chains=a.chains, align=a.align, n_or=a.n_or,
                 init=a.init, boundary_labels=int(a.boundary_labels), therm=a.therm, every=a.every, seed=a.seed,
                 positions=np.array(reps), mult=np.array([c[1] for c in cls]), seconds=time.time() - t0, partial=int(partial), n_done=m,
                 backend="gpu" if gpu else "cpu", kernel=a.kernel, kp=a.kp, D_therm=np.array(series),
                 **{k: np.array(v[:m]) for k, v in rec.items()})

    if sim.aligner is not None:
        for _ in range(20):
            if sim.aligner(sim.U, sim.W, max_pass=20) == 0:
                break
    for s in range(a.therm):
        sim.sweep()
        if s % 10 == 0 or s == a.therm - 1:
            series.append(sim.measure()["D"])
    for m in range(a.meas):
        for _ in range(a.every):
            sim.sweep()
        for k, v in sim.measure().items():
            rec.setdefault(k, []).append(v)
        rec.setdefault("plaq", []).append(sim.plaq())
        if m % 50 == 0 and m:
            save(m, True)
    save(a.meas, False)
    print(f"done {a.out} in {time.time() - t0:.0f}s", flush=True)
    return 0


# ====================================================================================================================== analysis (couple)

def blocks(x, nb=10):
    """mean and error of a series (n, ...) from nb consecutive blocks."""
    n = x.shape[0]
    nb = max(2, min(nb, n))
    idx = np.array_split(np.arange(n), nb)
    bm = np.stack([x[i].mean(axis=0) for i in idx])
    return bm.mean(axis=0), bm.std(axis=0, ddof=1) / math.sqrt(nb)


def verdict_u(r):
    """Rule U of PREREG.md section 4 (fixed in advance)."""
    if r["S"] >= 0.3:
        return "SATURATED (no bound)"
    stationary = abs(r["Q_U_first_half"] - r["Q_U_second_half"]) <= 4.5 * max(r["Q_U_err"], 1e-12)
    if r["S"] <= 0.1 and stationary:
        if r["Q_U"] + 3 * r["Q_U_err"] <= 0.9:
            return "INFORMATIVE: criterion supported on this box and boundary family"
        if r["Q_U"] > 1.0:
            return "INFORMATIVE, Q_U > 1: no statement (floor 8/nc = %.2f)" % r["floor"]
        return "INFORMATIVE, 0.9 < Q_U + 3 sigma, Q_U <= 1: no statement"
    return "no statement (S = %.2f, %s)" % (r["S"], "stationary" if stationary else "halves disagree")


def analyse_couple_file(z):
    """Per class: mean D, D(r); the one-box sum  Q_U = 8 sum_classes mult * D / nc^4  (8 faces) and K = mean over the face cells."""
    ch = int(z["chains"])
    D = z["D"]                                         # (n, B)
    n, B = D.shape
    cl = B // ch
    mult = z["mult"].astype(float)
    nc = int(z["ncell"])
    out = {"group": str(z["group"]), "beta": float(z["beta"]), "ell": int(z["ell"]), "ncell": nc, "bg": str(z["bg"]), "pert": str(z["pert"]),
           "init": str(z["init"]), "align": str(z["align"]), "n_or": int(z["n_or"]), "n_meas": n, "chains": ch}
    Dc = D.reshape(n, cl, ch).mean(axis=2)             # (n, classes)
    m, e = blocks(Dc)
    out["D_class"], out["D_class_err"] = m.tolist(), e.tolist()
    out["positions"] = z["positions"].tolist()
    out["mult"] = mult.tolist()
    # Q_U with its error from blocks of the combined series
    q_series = 8.0 * (Dc * mult[None, :]).sum(axis=1) / nc ** 4
    qm, qe = blocks(q_series[:, None])
    out["Q_U"], out["Q_U_err"] = float(qm[0]), float(qe[0])
    out["K"] = float((m * mult).sum() / mult.sum())
    h = n // 2
    out["Q_U_first_half"] = float(q_series[:h].mean())
    out["Q_U_second_half"] = float(q_series[h:].mean())
    Dr = z["Dr"].reshape(n, cl, ch, nc).mean(axis=2)   # (n, classes, nc)
    rm = (Dr * mult[None, :, None]).sum(axis=1) / mult.sum()
    out["D_r"], out["D_r_err"] = [x.tolist() for x in blocks(rm)]
    out["frac_link"] = float(z["frac"].mean())
    out["S"] = float(out["K"] / (4 * nc ** 4))     # fraction of the box cells that differ (rule U)
    out["floor"] = 8.0 / nc
    out["verdict"] = verdict_u(out)
    out["D_last_therm"] = float(np.mean(z["D_therm"][-1])) if "D_therm" in z.files and len(z["D_therm"]) else None
    out["plaq"] = float(z["plaq"].mean())
    # raw time series of the total D (mean over classes weighted) for the thermalisation check
    return out


def analyse(a):
    rows = []
    for p in sorted(glob.glob(os.path.join(a.dir, "*.npz"))):
        z = np.load(p, allow_pickle=False)
        if "D" not in z.files or int(z["partial"]):
            continue
        r = analyse_couple_file(z)
        r["file"] = os.path.basename(p)
        rows.append(r)
    import tiecore
    ties = tiecore.analyse_ties(a.dir)
    rows.sort(key=lambda r: (r["group"], r["beta"], r["bg"], r["pert"], r["ell"]))
    for r in rows:
        print(f"{r['file']:44s} Q_U = {r['Q_U']:8.3f} +- {r['Q_U_err']:.3f} (halves {r['Q_U_first_half']:.2f}/{r['Q_U_second_half']:.2f})  K = {r['K']:.3f}  "
              f"D(r) = " + " ".join(f"{x:.2f}" for x in r["D_r"]) + f"  link frac {r['frac_link']:.4f}  S = {r['S']:.3f}  -> {r['verdict']}")
    if a.out:
        json.dump({"couple": rows, "tie": ties}, open(a.out, "w"), indent=1)
    return 0


# ====================================================================================================================== selftest

def selftest(a):
    ok = True
    xp = np
    # 1. normalisation: ln Z against scipy
    from scipy.special import ive
    for k in (0.0, 0.3, 2.0, 9.0, 15.0):
        kk = np.array([max(k, 1e-9)])
        ref = np.log(ive(1, kk) / kk) + 0   # I1(k)/k e^{-k}
        got = lz_su2(np, kk) - kk
        ref0 = np.log(ive(0, kk))
        got0 = lz_u1(np, kk) - kk
        # constants: Z_su2 = pi I1/k  -> mean_j(...) approximates (1/pi) * integral...; compare differences instead
        if k == 0.0:
            base_s, base_u = got[0] - ref[0], got0[0] - ref0[0]
        d1, d2 = (got[0] - ref[0]) - base_s, (got0[0] - ref0[0]) - base_u
        good = abs(d1) < 1e-10 and abs(d2) < 1e-10
        ok &= good
        print(f"lnZ kappa={k}: SU(2) diff {d1:.1e}, U(1) diff {d2:.1e} -> {'ok' if good else 'FAIL'}")
    # 2. maximal coupling: marginals and agreement probability
    rng = RNG(np, 5)
    for group, A1, A2 in (("su2", np.array([1.2, 0.3, -0.2, 0.5]), np.array([1.0, 0.5, -0.1, 0.4])),
                          ("su2", np.array([0.2, 0.0, 0.0, 0.1]), np.array([0.2, 0.0, 0.0, 0.1])),
                          ("su2", np.array([3.0, 0.0, 0.0, 0.0]), np.array([-1.0, 1.5, 0.0, 0.0])),
                          ("u1", 1.3 + 0.4j, 1.0 + 0.9j)):
        law = Law(group, 1.3, np, rng)
        n = 200000
        a1 = np.tile(np.asarray(A1), (n, 1)) if group == "su2" else np.full(n, A1)
        a2 = np.tile(np.asarray(A2), (n, 1)) if group == "su2" else np.full(n, A2)
        U1, U2 = law.coupled(a1, a2)
        # marginals: E exp(beta Re(U A)) moments via independent samples from the same law
        S1, S2 = law.sample(a1), law.sample(a2)
        f = lambda U, A: law.expo(U, A)
        m1 = (f(U1, a2) - 0), (f(S1, a2) - 0)
        z1 = abs(m1[0].mean() - m1[1].mean()) / (m1[0].std() / math.sqrt(n) * 1.5)
        m2 = (f(U2, a1)), (f(S2, a1))
        z2 = abs(m2[0].mean() - m2[1].mean()) / (m2[0].std() / math.sqrt(n) * 1.5)
        same = float(np.mean(np.all(U1 == U2, axis=-1) if group == "su2" else (U1 == U2)))
        # TV by importance sampling from p1: E_p1 (1 - p2/p1)_+
        L = law.expo(S1, a2) - law.expo(S1, a1) + law.lz(a1) - law.lz(a2)
        tv = float(np.mean(np.maximum(1 - np.exp(L), 0)))
        good = z1 < 4 and z2 < 4 and abs(same - (1 - tv)) < 0.004
        ok &= good
        print(f"coupling {group}: marginal z-scores {z1:.1f}, {z2:.1f}; P(U1 = U2) = {same:.4f}, 1 - TV = {1 - tv:.4f} -> {'ok' if good else 'FAIL'}")
    print("selftest (part 1)", "OK" if ok else "FAIL")
    ok2 = selftest2()
    return 0 if (ok and ok2) else 1


def selftest2():
    """Part 2: sparse staples, gauge-copy recovery, identical pair stays identical, tie geometry, 2I group."""
    import tiecore
    ok = True
    for grp in ("su2", "u1"):
        box = bd.Box(6)
        B = 3
        U = bd.initial_links(grp, box, "hot", B, 1)
        rng = np.random.default_rng(2)
        for mu in range(4):
            if grp == "su2":
                r = rng.normal(size=U[mu].shape)
                r /= np.linalg.norm(r, axis=-1, keepdims=True)
                U[mu] = np.where(box.dyn[mu][None, ..., None], r, U[mu])
            else:
                U[mu] = np.where(box.dyn[mu][None], rng.uniform(-3, 3, U[mu].shape), U[mu])
        free = np.tile(box.interior.reshape(1, -1), (B, 1))
        sim = CoupledChains(grp, box, 2.3, U, [u.copy() for u in U], 5, np, free, nc=3, pos=np.zeros((B, 3), int))
        err = 0.0
        for mu in range(4):
            for p in (0, 1):
                err = max(err, float(np.abs(sim.staple(sim.U, mu)[:, sim.masks[mu][p]] - sim.staple_s(sim.U, mu, p)).max()))
        # identical pair stays identical through sweeps
        for _ in range(3):
            sim.sweep()
        d_ident = float(sim.measure()["D"].max())
        # gauge copy recovered by the alignment
        ops = bd.make_ops(grp, np)
        g = bd.random_gauge(grp, box, B, np.random.default_rng(3))
        V = bd.gauge_transform(ops, [u.copy() for u in sim.U], g)
        W = [np.where(box.dyn[mu].reshape((1,) + box.dims + ((1,) if grp == "su2" else ())), V[mu], sim.U[mu]) for mu in range(4)]
        sim2 = CoupledChains(grp, box, 2.3, sim.U, W, 6, np, free, nc=3, pos=np.zeros((B, 3), int))
        d0 = float(sim2.measure()["D"].min())
        sim2.aligner(sim2.U, sim2.W, max_pass=20)
        d1 = float(sim2.measure()["D"].max())
        good = err == 0.0 and d_ident == 0.0 and d0 > 0 and d1 == 0.0
        ok &= good
        print(f"{grp}: sparse staples {err:.1e}, identical pair after 3 sweeps D = {d_ident:.0f}, gauge copy D = {d0:.0f} -> {d1:.0f} after alignment -> {'ok' if good else 'FAIL'}")
    # tie geometry: equal area at ell = 4 s + 1
    for ell in (5, 9):
        box = bd.Box(ell)
        ops = bd.make_ops("z2", np)
        cnt = []
        for sec in "AB":
            U = tiecore.tie_state("z2", box, 1, 0, sec)
            n = 0
            for mu in range(4):
                for nu in range(mu + 1, 4):
                    P = ops.re(ops.mul(ops.mul(U[mu], bd.sh(U[nu], mu)), ops.mul(ops.dag(bd.sh(U[mu], nu)), ops.dag(U[nu]))))
                    dp = box.dyn[mu] | np.roll(box.dyn[nu], -1, axis=mu) | np.roll(box.dyn[mu], -1, axis=nu) | box.dyn[nu]
                    n += int(((P[0] < 0) & dp).sum())
            cnt.append(n)
        good = cnt[0] == cnt[1]
        ok &= good
        print(f"tie geometry ell = {ell}: frustrated dynamic plaquettes A {cnt[0]}, B {cnt[1]} -> {'ok' if good else 'FAIL'}")
    G = tiecore.i2_elements()
    S = {tuple(np.round(x, 9) + 0.0) for x in G}
    rng = np.random.default_rng(1)
    bad = 0
    for _ in range(2000):
        i, j = rng.integers(0, 120, 2)
        bad += tuple(np.round(bd.qmul(G[i], G[j]), 9) + 0.0) not in S
    good = G.shape == (120, 4) and bad == 0
    ok &= good
    print(f"2I: {G.shape[0]} elements, closure failures {bad} -> {'ok' if good else 'FAIL'}")
    print("selftest (part 2)", "OK" if ok else "FAIL")
    return ok


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("couple")
    r.add_argument("group", choices=("su2", "u1"))
    r.add_argument("beta", type=float)
    r.add_argument("ell", type=int)
    r.add_argument("bg", choices=("calm", "typical", "hot", "twist", "flux"))
    r.add_argument("out")
    r.add_argument("--ncell", type=int, default=3, help="cells per side of the box (cell side ell / ncell lattice units)")
    r.add_argument("--pert", choices=("flip", "rand", "gauge", "none"), default="flip")
    r.add_argument("--init", choices=("same", "hot", "indep", "rot"), default="same")
    r.add_argument("--positions", choices=("all", "centre", "corner"), default="all", help="symmetry classes of the changed cell")
    r.add_argument("--depth-cap", type=int, default=0, help="merge face-cell depths above this (strong-coupling anchors only)")
    r.add_argument("--align", choices=("ham", "none"), default="ham")
    r.add_argument("--boundary-labels", type=int, default=0, help="gauge control: allow the gauge labels at the changed boundary sites")
    r.add_argument("--chains", type=int, default=4, help="coupled pairs per class")
    r.add_argument("--therm", type=int, default=100)
    r.add_argument("--meas", type=int, default=200)
    r.add_argument("--every", type=int, default=2)
    r.add_argument("--n-or", type=int, default=0)
    r.add_argument("--kernel", choices=("hb", "metro"), default="hb", help="hb: coupled heat bath; metro: coupled Metropolis (vMF proposals, maximal coupling)")
    r.add_argument("--kp", type=float, default=40.0, help="metro: proposal concentration (step about 1/sqrt(kp))")
    r.add_argument("--n-hit", type=int, default=1)
    r.add_argument("--pre", type=int, default=100)
    r.add_argument("--periodic-therm", type=int, default=150)
    r.add_argument("--seed", type=int, default=1)
    r.add_argument("--cpu", action="store_true")
    t = sub.add_parser("tie")
    t.add_argument("group", choices=("su2", "z2", "i2"))
    t.add_argument("beta", type=float)
    t.add_argument("ell", type=int)
    t.add_argument("sector", choices=("A", "B"))
    t.add_argument("out")
    t.add_argument("--sep", type=int, default=0)
    t.add_argument("--chains", type=int, default=8)
    t.add_argument("--therm", type=int, default=200)
    t.add_argument("--nodes", type=int, default=7)
    t.add_argument("--step-therm", type=int, default=40)
    t.add_argument("--meas", type=int, default=100)
    t.add_argument("--every", type=int, default=2)
    t.add_argument("--n-or", type=int, default=3)
    t.add_argument("--seed", type=int, default=1)
    t.add_argument("--cpu", action="store_true")
    s = sub.add_parser("analyse")
    s.add_argument("dir")
    s.add_argument("--out", default=None)
    sub.add_parser("selftest")
    a = ap.parse_args()
    if a.cmd == "tie":
        import tiecore
        return tiecore.tie_run(a)
    return {"couple": couple_run, "analyse": analyse, "selftest": selftest}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
