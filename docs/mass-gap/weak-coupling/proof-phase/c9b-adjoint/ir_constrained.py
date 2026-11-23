"""c9b infrared pilot, part 1 of 2: constrained sampling of one coarse link's conditional law (PREREG-PILOT.md, PREREG-GPU.md section 3).

Fine SU(2) links U (unit quaternions, boundary.qmul's product convention) on a periodic N^4 lattice, direction 0 = time. Action
    S(U) = - sum_P [ F_c t_P + (A_c/3)(4 t_P^2 - 1) ]  -  kappa_c sum_{y in C} <V_y(U), w_y>
with t_P = (1/2) Re tr U_P, plane class c = ts / ss (Wilson: F = beta, A = 0), V_y the block variable of c3b's good blocking
(Blocking.lean `smearBlock w` iterated n times, b = 2^n, exactly as `../c3b-refit/goodblock.py`; cross-checked in `selftest`), C the
constrained coarse links (all coarse links within coarse L-infinity distance R of the target link's site, except the target x itself),
w_y their prescribed values, <., .> the R^4 inner product (= (1/2) Re tr V w^dagger). With n = 0 the "coarse" links are the fine ones
(used for the exact-law check on a coarse plaquette action).

Sampler: HMC with left-multiplicative updates U <- exp(eps P) U (P pure imaginary quaternions), the force from a small reverse-mode
differentiation of the whole computation (quaternion product, conjugation, roll, sum, scale, projection q/|q|, sublattice); fine links
outside the region are frozen. Recorded per trajectory and chain: V_x, the acceptance, dH, the constraint residual mean(1 - <V_y, w_y>).

CLI
  py ir_constrained.py selftest     seconds-scale smoke test: gradient vs finite differences, HMC reversibility, blocking vs goodblock.py
  py ir_constrained.py run ... --go  a pre-registered pilot run (PREREG-PILOT.md; needs the owner's OK)
numpy (or cupy with --gpu, not used in the pilot).
"""
import argparse
import importlib.util
import json
import math
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
TIME = 0


# ------------------------------------------------------------------------------------------------------------ quaternion algebra
def qmul(a, b, xp=np):
    a0, a1, a2, a3 = a
    b0, b1, b2, b3 = b
    return xp.stack([a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3,
                     a0 * b1 + b0 * a1 - (a2 * b3 - a3 * b2),
                     a0 * b2 + b0 * a2 - (a3 * b1 - a1 * b3),
                     a0 * b3 + b0 * a3 - (a1 * b2 - a2 * b1)])


def qdag(a, xp=np):
    return xp.concatenate([a[:1], -a[1:]])


def shift(x, off, xp=np):
    """Link field x (4, B, N, N, N, N): result at site y = x at y + off."""
    for mu, s in enumerate(off):
        if s:
            x = xp.roll(x, -s, axis=2 + mu)
    return x


def ev(mu, k):
    v = [0, 0, 0, 0]
    v[mu] = k
    return v


def vadd(*vs):
    return [sum(c) for c in zip(*vs)]


def transverse(mu):
    return [nu for nu in range(4) if nu != TIME and nu != mu]


# ------------------------------------------------------------------------------------------------------------ reverse-mode tape
class Node:
    __slots__ = ("val", "grad", "back")

    def __init__(self, val, back=None):
        self.val, self.grad, self.back = val, None, back


class Tape:
    def __init__(self, xp=np):
        self.xp, self.nodes = xp, []

    def _acc(self, n, g):
        n.grad = g if n.grad is None else n.grad + g

    def _new(self, val, back):
        n = Node(val, back)
        self.nodes.append(n)
        return n

    def leaf(self, val):
        return self._new(val, None)

    def roll(self, a, off):
        if not any(off):
            return a
        neg = [-o for o in off]
        return self._new(shift(a.val, off, self.xp), lambda g: self._acc(a, shift(g, neg, self.xp)))

    def mul(self, a, b):
        xp = self.xp
        return self._new(qmul(a.val, b.val, xp),
                         lambda g: (self._acc(a, qmul(g, qdag(b.val, xp), xp)), self._acc(b, qmul(qdag(a.val, xp), g, xp))))

    def dag(self, a):
        return self._new(qdag(a.val, self.xp), lambda g: self._acc(a, qdag(g, self.xp)))

    def add(self, *xs):
        v = xs[0].val
        for x in xs[1:]:
            v = v + x.val

        def back(g):
            for x in xs:
                self._acc(x, g)
        return self._new(v, back)

    def scale(self, a, c):
        return self._new(c * a.val, lambda g: self._acc(a, c * g))

    def proj(self, a):
        xp = self.xp
        n = xp.sqrt((a.val * a.val).sum(axis=0, keepdims=True))
        q = a.val / n

        def back(g):
            self._acc(a, (g - (q * g).sum(axis=0, keepdims=True) * q) / n)
        return self._new(q, back)

    def sub(self, a, b):
        """Sublattice of stride b (origin 0)."""
        if b == 1:
            return a
        xp = self.xp
        sl = (slice(None), slice(None)) + (slice(None, None, b),) * 4

        def back(g):
            z = xp.zeros_like(a.val)
            z[sl] = g
            self._acc(a, z)
        return self._new(a.val[sl], back)

    def take(self, a, off, stride):
        """Periodic strided sampling: result at grid point i = a at (off + stride i) mod M, per axis (injective)."""
        xp = self.xp
        M = a.val.shape[2]
        m = M // stride
        idx = [xp.asarray((off[i] + stride * np.arange(m)) % M) for i in range(4)]
        ix = (slice(None), slice(None), idx[0][:, None, None, None], idx[1][None, :, None, None],
              idx[2][None, None, :, None], idx[3][None, None, None, :])

        def back(g):
            z = xp.zeros_like(a.val)
            z[ix] = g
            self._acc(a, z)
        return self._new(a.val[ix], back)

    def backward(self, seeds):
        for n, g in seeds:
            self._acc(n, g)
        for n in reversed(self.nodes):
            if n.grad is not None and n.back is not None:
                n.back(n.grad)


# ------------------------------------------------------------------------------------------------------------ blocking and action
def smear_step(T, F, lg, w):
    """One step of smearBlock on the full grid: F[mu] links of length lg (fine units); straight path + w * spatial staples, projected."""
    out = []
    for mu in range(4):
        terms = [T.mul(F[mu], T.roll(F[mu], ev(mu, lg)))]
        for nu in transverse(mu):
            up = T.mul(T.mul(T.mul(F[nu], T.roll(F[mu], ev(nu, lg))), T.roll(F[mu], vadd(ev(nu, lg), ev(mu, lg)))),
                       T.dag(T.roll(F[nu], ev(mu, 2 * lg))))
            dn = T.mul(T.mul(T.mul(T.dag(T.roll(F[nu], ev(nu, -lg))), T.roll(F[mu], ev(nu, -lg))),
                             T.roll(F[mu], vadd(ev(nu, -lg), ev(mu, lg)))),
                       T.roll(F[nu], vadd(ev(nu, -lg), ev(mu, 2 * lg))))
            terms += [T.scale(up, w), T.scale(dn, w)]
        out.append(T.proj(T.add(*terms)))
    return out


def coarse_links(T, U, n, w):
    """Level-n block variables on the coarse lattice with origin 0 (stride b = 2^n); n = 0: the fine links."""
    F = U
    for k in range(1, n + 1):
        F = smear_step(T, F, 2 ** (k - 1), w)
    return [T.sub(F[mu], 2 ** n) for mu in range(4)]


def smear_step_strided(T, F, w):
    """The same step as smear_step, evaluated only on the output sublattice: F on a grid of side M with links of length 1 grid
    unit; output on the grid of side M/2 (stride 2, origin 0), links of length 1 output unit. As goodblock.py's take_at."""
    def at(x, off):
        return T.take(x, off, 2)
    out = []
    for mu in range(4):
        o = [0, 0, 0, 0]
        terms = [T.mul(at(F[mu], o), at(F[mu], ev(mu, 1)))]
        for nu in transverse(mu):
            up = T.mul(T.mul(T.mul(at(F[nu], o), at(F[mu], ev(nu, 1))), at(F[mu], vadd(ev(nu, 1), ev(mu, 1)))),
                       T.dag(at(F[nu], ev(mu, 2))))
            dn = T.mul(T.mul(T.mul(T.dag(at(F[nu], ev(nu, -1))), at(F[mu], ev(nu, -1))), at(F[mu], vadd(ev(nu, -1), ev(mu, 1)))),
                       at(F[nu], vadd(ev(nu, -1), ev(mu, 2))))
            terms += [T.scale(up, w), T.scale(dn, w)]
        out.append(T.proj(T.add(*terms)))
    return out


def coarse_links_strided(T, U, n, w):
    """As coarse_links, computing each level only where the next one needs it (memory about 1/16 per level)."""
    F = U
    for _ in range(n):
        F = smear_step_strided(T, F, w)
    return F


class Model:
    """Couplings, constraint data and masks. cpl = dict(F_ts, F_ss, A_ts, A_ss)."""

    def __init__(self, N, n, w, cpl, kappa, xp=np, lean=False):
        self.N, self.n, self.w, self.cpl, self.kappa, self.xp = N, n, w, cpl, kappa, xp
        self.lean = lean  # strided blocking + plane-by-plane plaquette gradient (same values; selftest compares)
        self.b = 2 ** n
        self.Nc = N // self.b
        self.target = None  # (4 mu, 4, B, Nc^4) prescribed coarse values
        self.cmask = None   # (4 mu, 1, B, Nc^4) 1 on constrained coarse links
        self.dyn = None     # (4 mu, 1, B, N^4) 1 on dynamic fine links
        self.mass = None    # (4 mu, 1, B, N^4) kinetic mass per fine link (None: 1); any positive choice keeps HMC exact

    def evaluate(self, U, need_grad=True):
        """S(U) per chain (B,) and, if need_grad, dS/dU in R^4 per link (same shape as U)."""
        if self.lean:
            return self.evaluate_lean(U, need_grad)
        xp = self.xp
        T = Tape(xp)
        L = [T.leaf(U[mu]) for mu in range(4)]
        S = 0.0
        seeds = []
        for mu in range(4):
            for nu in range(mu + 1, 4):
                c = "ts" if TIME in (mu, nu) else "ss"
                Fc, Ac = self.cpl["F_" + c], self.cpl["A_" + c]
                P = T.mul(T.mul(L[mu], T.roll(L[nu], ev(mu, 1))), T.mul(T.dag(T.roll(L[mu], ev(nu, 1))), T.dag(L[nu])))
                t = P.val[0]
                S = S - (Fc * t + (Ac / 3) * (4 * t * t - 1)).reshape(t.shape[0], -1).sum(axis=1)
                if need_grad:
                    g = xp.zeros_like(P.val)
                    g[0] = -(Fc + (8 * Ac / 3) * t)
                    seeds.append((P, g))
        if self.kappa and self.target is not None:
            V = coarse_links(T, L, self.n, self.w)
            for mu in range(4):
                dot = (V[mu].val * self.target[mu]).sum(axis=0) * self.cmask[mu][0]
                S = S - self.kappa * dot.reshape(dot.shape[0], -1).sum(axis=1)
                if need_grad:
                    seeds.append((V[mu], -self.kappa * self.target[mu] * self.cmask[mu]))
        if not need_grad:
            return S, None
        T.backward(seeds)
        G = xp.stack([L[mu].grad if L[mu].grad is not None else xp.zeros_like(U[mu]) for mu in range(4)])
        return S, G

    def evaluate_lean(self, U, need_grad=True):
        """As evaluate, with one small tape per plaquette plane and the strided blocking (peak memory far lower)."""
        xp = self.xp
        S = 0.0
        G = xp.zeros_like(U) if need_grad else None
        for mu in range(4):
            for nu in range(mu + 1, 4):
                c = "ts" if TIME in (mu, nu) else "ss"
                Fc, Ac = self.cpl["F_" + c], self.cpl["A_" + c]
                T = Tape(xp)
                Lm, Ln = T.leaf(U[mu]), T.leaf(U[nu])
                P = T.mul(T.mul(Lm, T.roll(Ln, ev(mu, 1))), T.mul(T.dag(T.roll(Lm, ev(nu, 1))), T.dag(Ln)))
                t = P.val[0]
                S = S - (Fc * t + (Ac / 3) * (4 * t * t - 1)).reshape(t.shape[0], -1).sum(axis=1)
                if need_grad:
                    g = xp.zeros_like(P.val)
                    g[0] = -(Fc + (8 * Ac / 3) * t)
                    T.backward([(P, g)])
                    G[mu] += Lm.grad
                    G[nu] += Ln.grad
                del T, P
        if self.kappa and self.target is not None:
            T = Tape(xp)
            L = [T.leaf(U[mu]) for mu in range(4)]
            V = coarse_links_strided(T, L, self.n, self.w) if self.n > 0 else L
            seeds = []
            for mu in range(4):
                dot = (V[mu].val * self.target[mu]).sum(axis=0) * self.cmask[mu][0]
                S = S - self.kappa * dot.reshape(dot.shape[0], -1).sum(axis=1)
                if need_grad:
                    seeds.append((V[mu], -self.kappa * self.target[mu] * self.cmask[mu]))
            if need_grad:
                T.backward(seeds)
                for mu in range(4):
                    if L[mu].grad is not None:
                        G[mu] += L[mu].grad
            del T
        return S, G

    def precond_mass(self, U, nprobe, rng):
        """Kinetic mass per fine link M_l = 1 + kappa_c h_l, h_l = (1/3) E_r |Im(J_l^T r U_l^dagger)|^2: the Gauss-Newton diagonal of the
        penalty Hessian (sum over constrained coarse links of the squared sensitivity of V_y to link l), by nprobe random probes r on
        the coarse links. Computed once at the start; constant during the run, so HMC stays exact (REDESIGN.md)."""
        xp = self.xp
        acc = xp.zeros((4, 1) + U.shape[2:])
        for _ in range(nprobe):
            T = Tape(xp)
            L = [T.leaf(U[mu]) for mu in range(4)]
            V = coarse_links_strided(T, L, self.n, self.w) if self.n > 0 else L
            r = [xp.asarray(rng.normal(size=V[mu].val.shape)) * self.cmask[mu] for mu in range(4)]
            T.backward([(V[mu], r[mu]) for mu in range(4)])
            G = xp.stack([L[mu].grad if L[mu].grad is not None else xp.zeros_like(U[mu]) for mu in range(4)])
            rest = tuple(range(2, G.ndim))
            f = qmul(G.transpose(1, 0, *rest), qdag(U.transpose(1, 0, *rest), xp), xp)[1:].transpose(1, 0, *rest)
            acc = acc + (f * f).sum(axis=1, keepdims=True) / 3
        h = acc / nprobe
        M = 1.0 + self.kappa * h
        if self.dyn is not None:
            M = xp.where(self.dyn > 0, M, 1.0)
        return M

    def coarse(self, U):
        T = Tape(self.xp)
        L = [T.leaf(U[mu]) for mu in range(4)]
        if self.lean:
            V = coarse_links_strided(T, L, self.n, self.w) if self.n > 0 else L
        else:
            V = coarse_links(T, L, self.n, self.w)
        return self.xp.stack([v.val for v in V])

    def force(self, U):
        """Lie-algebra force Im(G U^dagger) (3 components), zero on frozen links; and S."""
        S, G = self.evaluate(U)
        rest = tuple(range(2, G.ndim))
        f = qmul(G.transpose(1, 0, *rest), qdag(U.transpose(1, 0, *rest), self.xp), self.xp)  # (4 comp, 4 mu, ...)
        f = f[1:].transpose(1, 0, *range(2, f.ndim))  # (4 mu, 3, B, N^4)
        if self.dyn is not None:
            f = f * self.dyn
        return S, f


def qexp_left(P, U, eps, xp=np):
    """exp(eps P) U for pure imaginary P (4 mu, 3, ...)."""
    th = eps * xp.sqrt((P * P).sum(axis=1, keepdims=True))
    s = xp.where(th > 1e-300, xp.sin(th) / xp.maximum(th, 1e-300), 1.0) * eps
    E = xp.concatenate([xp.cos(th), s * P], axis=1)  # (4 mu, 4, ...)
    out = qmul(E.transpose(1, 0, *range(2, E.ndim)), U.transpose(1, 0, *range(2, U.ndim)), xp)
    out = out.transpose(1, 0, *range(2, out.ndim))
    return out / xp.sqrt((out * out).sum(axis=1, keepdims=True))


def leapfrog(model, U, P, eps, nleap):
    xp = model.xp
    Minv = 1.0 if model.mass is None else 1.0 / model.mass
    S, f = model.force(U)
    P = P - 0.5 * eps * f
    for k in range(nleap):
        U = qexp_left(P * Minv, U, eps, xp)
        S, f = model.force(U)
        P = P - (eps if k < nleap - 1 else 0.5 * eps) * f
    return U, P, S


def hmc_step(model, U, eps, nleap, rng):
    xp = model.xp
    M = 1.0 if model.mass is None else model.mass
    P = xp.asarray(rng.normal(size=(4, 3) + U.shape[2:])) * xp.sqrt(M)
    if model.dyn is not None:
        P = P * model.dyn

    def kin(Q):
        return 0.5 * (Q * Q / M).reshape(4, 3, Q.shape[2], -1).sum(axis=(0, 1, 3))
    S0, _ = model.evaluate(U, need_grad=False)
    H0 = kin(P) + S0
    U1, P1, S1 = leapfrog(model, U, P, eps, nleap)
    H1 = kin(P1) + S1
    dH = H1 - H0
    acc = xp.asarray(rng.random(dH.shape)) < xp.exp(-dH)
    sel = acc.reshape((1, 1, -1) + (1,) * 4)
    return xp.where(sel, U1, U), acc, dH


# ------------------------------------------------------------------------------------------------------------ helpers
def random_su2(shape, rng):
    g = rng.normal(size=(4,) + shape)
    return g / np.linalg.norm(g, axis=0, keepdims=True)


def cold(N, B):
    U = np.zeros((4, 4, B) + (N,) * 4)
    U[:, 0] = 1.0
    return U


def coupling(action, beta=None):
    if action == "wilson":
        return dict(F_ts=beta, F_ss=beta, A_ts=0.0, A_ss=0.0)
    if action == "fit280":  # c3b base fit at L sqrt(sigma) = 2.80, central values (analysis.log)
        return dict(F_ts=0.054, F_ss=0.171, A_ts=-0.000595, A_ss=0.00149)
    raise ValueError(action)


def masks(model, B, xsite, xmu, R):
    """Constraint mask (coarse links within L-inf distance R of the coarse site xsite, except (xsite, xmu)) and dynamic fine links (the
    fine sites of those coarse cells)."""
    Nc, b, N = model.Nc, model.b, model.N

    def d(c):
        return min(abs(c), Nc - abs(c))
    near = np.zeros((Nc,) * 4, bool)
    for idx in np.ndindex(*(Nc,) * 4):
        near[idx] = max(d(idx[i] - xsite[i]) for i in range(4)) <= R
    cm = np.repeat(near[None, None, None], 4, axis=0).astype(float)
    cm = np.repeat(cm, B, axis=2)
    cm[(xmu, 0, slice(None)) + tuple(xsite)] = 0.0
    fine = np.kron(near.astype(float), np.ones((b,) * 4)) if b > 1 else near.astype(float)
    dyn = np.repeat(np.repeat(fine[None, None, None], 4, axis=0), B, axis=2)
    return cm, dyn


def move_quat(kind, delta):
    if kind == "none":
        return np.array([1.0, 0, 0, 0]), 0.0
    phi = {"flip": math.pi, "rot": math.pi / 4, "small": delta}[kind]
    return np.array([math.cos(phi), 0, 0, math.sin(phi)]), phi


# ------------------------------------------------------------------------------------------------------------ selftest (smoke)
def selftest(a):
    rng = np.random.default_rng(7)
    ok = True
    # 1. gradient vs central finite differences, blocking on (4^4 lattice, n = 1, fit280 couplings, random targets)
    N, B = 4, 1
    m = Model(N, 1, 2.0, coupling("fit280"), kappa=3.0)
    U = random_su2((4, B) + (N,) * 4, rng).transpose(1, 0, 2, 3, 4, 5, 6)
    m.target = random_su2((4, B) + (m.Nc,) * 4, rng).transpose(1, 0, 2, 3, 4, 5, 6)
    m.cmask, m.dyn = masks(m, B, (0, 0, 0, 0), 1, 9)
    S, f = m.force(U)
    X = rng.normal(size=f.shape)
    h = 1e-5
    Sp, _ = m.evaluate(qexp_left(X, U, h), need_grad=False)
    Sm, _ = m.evaluate(qexp_left(X, U, -h), need_grad=False)
    fd = (Sp - Sm) / (2 * h)
    an = (f * X).reshape(4, 3, B, -1).sum(axis=(0, 1, 3))
    rel = float(np.abs(fd - an).max() / np.abs(an).max())
    print(f"force vs finite differences (blocking n = 1, penalty on): relative error {rel:.1e}")
    ok &= rel < 1e-6
    # 2. HMC reversibility and energy conservation (n = 1, kappa = 3)
    P = rng.normal(size=f.shape)
    U1, P1, _ = leapfrog(m, U, P, 0.02, 10)
    U2, P2, _ = leapfrog(m, U1, -P1, 0.02, 10)
    rev = float(np.abs(U2 - U).max())
    print(f"leapfrog reversibility: max |U_back - U| = {rev:.1e}")
    ok &= rev < 1e-9
    dHs = []
    for eps in (0.04, 0.02):
        S0, _ = m.evaluate(U, need_grad=False)
        Ue, Pe, Se = leapfrog(m, U, P, eps, int(round(0.4 / eps)))
        dHs.append(float(abs(0.5 * (Pe * Pe).sum() + Se[0] - 0.5 * (P * P).sum() - S0[0])))
    ratio = dHs[0] / max(dHs[1], 1e-300)
    print(f"|dH| at eps 0.04, 0.02: {dHs[0]:.2e}, {dHs[1]:.2e} (ratio {ratio:.1f}; leapfrog: about 4)")
    ok &= 2.5 < ratio < 6
    # 3. blocking against goodblock.py (8^4, n = 2, random field)
    spec = importlib.util.spec_from_file_location("goodblock", os.path.join(HERE, "..", "c3b-refit", "goodblock.py"))
    gb = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gb)
    ops = gb.BL.make_ops("su2", np)
    N = 8
    U = random_su2((4, 1) + (N,) * 4, rng).transpose(1, 0, 2, 3, 4, 5, 6)
    H = gb.good_levels(ops, [U[mu] for mu in range(4)], 2, 2.0)
    ref = gb.coarse(ops, H, [U[mu] for mu in range(4)], 2)
    mine = Model(N, 2, 2.0, coupling("fit280"), 0.0).coarse(U)
    err = max(float(np.abs(mine[mu][:, 0] - ref[mu][:, 0]).max()) for mu in range(4))
    print(f"block variable (n = 2, w = 2) against goodblock.coarse, origin 0: max difference {err:.1e}")
    ok &= err < 1e-12
    # 3b. the lean implementation (strided blocking, plane-by-plane gradient) agrees with the default one (8^4, n = 2, penalty on)
    md = Model(8, 2, 2.0, coupling("fit280"), kappa=5.0)
    ml = Model(8, 2, 2.0, coupling("fit280"), kappa=5.0, lean=True)
    U = random_su2((4, 1) + (8,) * 4, rng).transpose(1, 0, 2, 3, 4, 5, 6)
    tg = random_su2((4, 1) + (2,) * 4, rng).transpose(1, 0, 2, 3, 4, 5, 6)
    for mm in (md, ml):
        mm.target = tg
        mm.cmask, mm.dyn = masks(mm, 1, (0, 0, 0, 0), 1, 9)
    Sd, Gd = md.evaluate(U)
    Sl, Gl = ml.evaluate(U)
    dv = float(np.abs(md.coarse(U) - ml.coarse(U)).max())
    dS = float(np.abs(Sd - Sl).max() / np.abs(Sd).max())
    dG = float(np.abs(Gd - Gl).max() / np.abs(Gd).max())
    print(f"lean vs default (8^4, n = 2): block variables {dv:.1e}, action {dS:.1e}, gradient {dG:.1e} (relative)")
    ok &= dv < 1e-12 and dS < 1e-12 and dG < 1e-10
    # 3c. preconditioning mass (n = 1, kappa = 5): >= 1 on dynamic links, and leapfrog with it is reversible
    mp = Model(4, 1, 2.0, coupling("fit280"), kappa=5.0, lean=True)
    U = random_su2((4, 1) + (4,) * 4, rng).transpose(1, 0, 2, 3, 4, 5, 6)
    mp.target = random_su2((4, 1) + (2,) * 4, rng).transpose(1, 0, 2, 3, 4, 5, 6)
    mp.cmask, mp.dyn = masks(mp, 1, (0, 0, 0, 0), 1, 9)
    mp.mass = mp.precond_mass(U, 4, rng)
    P = rng.normal(size=(4, 3, 1) + (4,) * 4) * np.sqrt(mp.mass)
    U1, P1, _ = leapfrog(mp, U, P, 0.02, 10)
    U2, _, _ = leapfrog(mp, U1, -P1, 0.02, 10)
    rv = float(np.abs(U2 - U).max())
    print(f"preconditioning mass: min {float(mp.mass.min()):.3f}, max {float(mp.mass.max()):.3f}; leapfrog with mass reversible: {rv:.1e}")
    ok &= float(mp.mass.min()) >= 1.0 and np.isfinite(mp.mass).all() and rv < 1e-9
    # 4. a few trajectories run end to end (tiny lattice; smoke only, no result-bearing numbers)
    m = Model(4, 1, 2.0, coupling("wilson", 0.5), kappa=20.0)
    U = cold(4, 1)
    m.target = m.coarse(U)
    m.cmask, m.dyn = masks(m, 1, (0, 0, 0, 0), 1, 9)
    t0 = time.time()
    accs = []
    for _ in range(3):
        U, acc, dH = hmc_step(m, U, 0.05, 5, rng)
        accs.append(bool(acc[0]))
    print(f"3 trajectories on 4^4 ran in {time.time() - t0:.1f} s (smoke)")
    ok &= np.all(np.isfinite(U))
    print("SELFTEST", "OK" if ok else "FAIL")
    return 0 if ok else 1


# ------------------------------------------------------------------------------------------------------------ run (pre-registered)
def run(a):
    if not a.go:
        print("run is a pre-registered pilot run; it starts only with --go after the owner's OK (PREREG-PILOT.md).")
        return 2
    rng = np.random.default_rng(a.seed)
    cpl = coupling(a.action, a.beta)
    m = Model(a.N, a.n, a.w, cpl, kappa=0.0)
    B = a.B
    xsite = tuple(int(c) for c in a.x.split(",")[:4])
    xmu = int(a.x.split(",")[4])
    ysite = tuple(int(c) for c in a.y.split(",")[:4])
    ymu = int(a.y.split(",")[4])
    m.cmask, m.dyn = masks(m, B, xsite, xmu, a.R)
    t_start = time.time()
    # background
    U = cold(a.N, B)
    if a.background == "typical":
        U1 = cold(a.N, 1)
        m1 = Model(a.N, a.n, a.w, cpl, kappa=0.0)
        rng_bg = np.random.default_rng(a.bgseed)  # the background depends on bgseed only: shared by the ensembles compared
        for _ in range(a.npre):
            U1, _, _ = hmc_step(m1, U1, a.eps, a.nleap, rng_bg)
        U = np.repeat(U1, B, axis=2)
    base = m.coarse(U)  # (4 mu, 4, B, Nc^4)
    R, phi = move_quat(a.move, a.delta)
    m.target = base.copy()
    m.kappa = a.kappa
    if a.n == 0 and a.pin_mass:
        m.mass = 1.0 + a.kappa * m.cmask  # pinned links: frequency about 1 instead of sqrt(kappa)
    # step-size tuning at the final kappa on the unmoved target (pre-registered rule): halve eps, double nleap until acceptance >= 0.6
    eps, nleap = a.eps, a.nleap
    tuning = []
    for _ in range(a.tune_max):
        accs = []
        for _ in range(a.tune_traj):
            U, acc, _ = hmc_step(m, U, eps, nleap, rng)
            accs.append(float(np.mean(acc)))
        tuning.append((eps, nleap, float(np.mean(accs))))
        if np.mean(accs) >= 0.6:
            break
        eps, nleap = eps / 2, nleap * 2
    # anneal the move at y along w_y exp(t phi k), t = 0..1, and the penalty from kappa/10 to kappa
    if a.n == 0:
        # the coarse links are the fine ones: apply the move at once and put every pinned link on its target (no anneal needed)
        wy = base[(ymu, slice(None), slice(None)) + ysite]
        m.target[(ymu, slice(None), slice(None)) + ysite] = qmul(wy, R[:, None] * np.ones_like(wy))
        U = np.where(m.cmask > 0, m.target, U)
        a.nanneal = 0
    log = {"acc": [], "dH": [], "resid": [], "vx": [], "resid_y": []}
    stopped = None
    for k in range(a.nanneal + a.ntherm + a.ntraj):
        t = min(1.0, (k + 1) / max(a.nanneal, 1))
        if k < a.nanneal:
            ang = t * phi
            Rt = np.array([math.cos(ang), 0, 0, math.sin(ang)])
            wy = base[(ymu, slice(None), slice(None)) + ysite]
            m.target[(ymu, slice(None), slice(None)) + ysite] = qmul(wy, Rt[:, None] * np.ones_like(wy))
        if time.time() - t_start > a.max_wall:
            stopped = k
            break
        U, acc, dH = hmc_step(m, U, eps, nleap, rng)
        if k >= a.nanneal + a.ntherm:
            V = m.coarse(U)
            vx = V[(xmu, slice(None), slice(None)) + xsite]  # (4, B)
            resid = 1 - ((V * m.target).sum(axis=1, keepdims=True) * m.cmask).reshape(4, B, -1).sum(axis=(0, 2)) / \
                m.cmask.reshape(4, B, -1).sum(axis=(0, 2))
            log["vx"].append(vx.T.copy())
            log["acc"].append(acc.copy())
            log["dH"].append(dH.copy())
            log["resid"].append(resid.copy())
            wyt = m.target[(ymu, slice(None), slice(None)) + ysite]
            log["resid_y"].append(1 - (V[(ymu, slice(None), slice(None)) + ysite] * wyt).sum(axis=0))
    wall = time.time() - t_start
    np.savez(a.out, vx=np.array(log["vx"]), acc=np.array(log["acc"]), dH=np.array(log["dH"]), resid=np.array(log["resid"]),
             resid_y=np.array(log["resid_y"]), tuning=np.array(tuning), args=json.dumps(vars(a)), wall=wall,
             stopped=-1 if stopped is None else stopped)
    print(json.dumps({"out": a.out, "wall_s": wall, "acc": float(np.mean(log["acc"])), "resid": float(np.mean(log["resid"])),
                      "resid_y": float(np.mean(log["resid_y"])), "tuning": tuning, "eps": eps, "nleap": nleap,
                      "n_meas": len(log["vx"]), "stopped_at": stopped}))
    return 0


class DevRng:
    """numpy-Generator-like normal/random on the device (cupy's Generator has standard_normal and random)."""

    def __init__(self, xp, seed):
        self.g = xp.random.default_rng(seed)

    def normal(self, size):
        return self.g.standard_normal(size)

    def random(self, shape):
        return self.g.random(shape)


def to_host(x):
    return x.get() if hasattr(x, "get") else np.asarray(x)


def timing(a):
    """The GPU timing job (TIMING.md): one ensemble at the primary point, measuring wall time per trajectory, acceptance after the
    tuning rule, tau_int of V_x, and device memory. Writes a progress line per trajectory (for the external watcher) and saves
    every 10 trajectories; stops itself at --max-wall (the watcher kills at the hard cap regardless)."""
    if not a.go:
        print("timing is the owner-approved GPU timing job; it starts only with --go (TIMING.md).")
        return 2
    t_start = time.time()
    if a.gpu:
        import cupy as xp
    else:
        xp = np
    prog = open(a.progress, "w", buffering=1)

    def note(**kw):
        kw["elapsed"] = round(time.time() - t_start, 1)
        prog.write(json.dumps(kw) + "\n")

    cpl = coupling(a.action, a.beta)
    m = Model(a.N, a.n, a.w, cpl, kappa=0.0, xp=xp, lean=True)
    B = a.B
    xsite = tuple(int(c) for c in a.x.split(",")[:4])
    xmu = int(a.x.split(",")[4])
    # background: heat bath + overrelaxation (c3b's updater, Leg C's module), one chain, copied to the B chains
    spec = importlib.util.spec_from_file_location("goodblock", os.path.join(HERE, "..", "c3b-refit", "goodblock.py"))
    gb = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gb)
    upd = gb.BL.make_updater("su2", gb.BL.PeriodicBox(a.N), a.beta, 1, a.bgseed, a.gpu, False)
    for k in range(a.npre):
        upd.sweep(3)
        if k % 20 == 0:
            note(stage="background", sweep=k)
    U1 = xp.stack([xp.asarray(u) for u in gb.chain_q("su2", xp, upd, 0)])  # (4 mu, 4, 1, N^4)
    del upd
    if a.gpu:
        xp.get_default_memory_pool().free_all_blocks()
    U = xp.repeat(U1, B, axis=2)
    note(stage="background done", plaq=float(to_host(U1[:, 0]).mean()))
    cm, dyn = masks(m, B, xsite, xmu, a.R)
    m.cmask, m.dyn = xp.asarray(cm), xp.asarray(dyn)
    m.target = m.coarse(U).copy()
    m.kappa = a.kappa
    rng = DevRng(xp, a.seed) if a.gpu else np.random.default_rng(a.seed)
    eps, nleap = a.eps, a.nleap
    tuning = []
    for _ in range(a.tune_max):
        accs = []
        for _ in range(a.tune_traj):
            t0 = time.time()
            U, acc, dH = hmc_step(m, U, eps, nleap, rng)
            accs.append(float(to_host(acc).mean()))
            note(stage="tune", eps=eps, nleap=nleap, acc=accs[-1], dH=float(to_host(dH).mean()), s_traj=round(time.time() - t0, 3))
            if time.time() - t_start > a.max_wall:
                break
        tuning.append((eps, nleap, float(np.mean(accs))))
        if np.mean(accs) >= 0.6 or time.time() - t_start > a.max_wall:
            break
        eps, nleap = eps / 2, nleap * 2
    mem = int(xp.get_default_memory_pool().total_bytes()) if a.gpu else 0
    log = {"vx": [], "acc": [], "dH": [], "s_traj": []}

    def save():
        np.savez(a.out, vx=np.array(log["vx"]), acc=np.array(log["acc"]), dH=np.array(log["dH"]), s_traj=np.array(log["s_traj"]),
                 tuning=np.array(tuning), args=json.dumps(vars(a)), mem_bytes=mem, eps=eps, nleap=nleap,
                 wall=time.time() - t_start)
    k = 0
    while time.time() - t_start < a.max_wall and k < a.ntraj:
        t0 = time.time()
        U, acc, dH = hmc_step(m, U, eps, nleap, rng)
        V = m.coarse(U)
        log["vx"].append(to_host(V[(xmu, slice(None), slice(None)) + xsite]).T.copy())
        log["acc"].append(to_host(acc))
        log["dH"].append(to_host(dH))
        log["s_traj"].append(time.time() - t0)
        note(stage="production", traj=k, acc=float(log["acc"][-1].mean()), s_traj=round(log["s_traj"][-1], 3))
        k += 1
        if k % 10 == 0:
            save()
    save()
    note(stage="DONE", n_traj=k)
    print(json.dumps({"out": a.out, "wall_s": time.time() - t_start, "n_traj": k, "eps": eps, "nleap": nleap, "tuning": tuning,
                      "s_per_traj_median": float(np.median(log["s_traj"])) if k else None,
                      "acc": float(np.mean(log["acc"])) if k else None, "mem_GB": mem / 1e9}))
    return 0


def tune(a):
    """THE TUNING PRE-STEP (PREREG-PILOT2.md): per kappa_c, the preconditioning mass, the step-size rule, then n_meas trajectories to
    measure acceptance, seconds per trajectory and tau_int (V_x components, the action S). No production, no physics numbers."""
    if not a.go:
        print("tune is the pre-registered tuning pre-step; it runs only with --go (PREREG-PILOT2.md).")
        return 2
    t_start = time.time()
    xp = np
    cpl = coupling(a.action, a.beta)
    B = a.B
    xsite = tuple(int(c) for c in a.x.split(",")[:4])
    xmu = int(a.x.split(",")[4])
    # background: c3b's heat bath + overrelaxation (CPU updater), one configuration
    spec = importlib.util.spec_from_file_location("goodblock", os.path.join(HERE, "..", "c3b-refit", "goodblock.py"))
    gb = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gb)
    upd = gb.BL.make_updater("su2", gb.BL.PeriodicBox(a.N), a.beta, 1, a.bgseed, False, False)
    for _ in range(a.npre):
        upd.sweep(3)
    U0 = np.stack([np.asarray(u) for u in gb.chain_q("su2", np, upd, 0)])
    del upd
    U0 = np.repeat(U0, B, axis=2)
    t_bg = time.time() - t_start
    rng = np.random.default_rng(a.seed)
    out = {"setting": vars(a).copy(), "t_background_s": t_bg, "per_kappa": []}
    out["setting"].pop("func", None)
    import ir_condlaw as cl
    for kappa in [float(k) for k in a.kappas.split(",")]:
        t_k = time.time()
        m = Model(a.N, a.n, a.w, cpl, kappa=kappa, lean=True)
        m.cmask, m.dyn = masks(m, B, xsite, xmu, a.R)
        U = U0.copy()
        m.target = m.coarse(U).copy()
        t0 = time.time()
        m.mass = m.precond_mass(U, a.nprobe, rng) if a.precond else None
        t_mass = time.time() - t0
        eps, nleap = a.eps, a.nleap
        tuning = []
        for _ in range(a.tune_max):
            accs, ts = [], []
            for _ in range(a.tune_traj):
                t1 = time.time()
                U, acc, _ = hmc_step(m, U, eps, nleap, rng)
                ts.append(time.time() - t1)
                accs.append(float(np.mean(acc)))
            tuning.append({"eps": eps, "nleap": nleap, "acc": float(np.mean(accs)), "s_traj": float(np.median(ts))})
            if np.mean(accs) >= 0.6:
                break
            eps, nleap = eps / 2, nleap * 2
        vx, S, accm, ts = [], [], [], []
        for _ in range(a.n_meas):
            t1 = time.time()
            U, acc, _ = hmc_step(m, U, eps, nleap, rng)
            ts.append(time.time() - t1)
            accm.append(float(np.mean(acc)))
            V = m.coarse(U)
            vx.append(V[(xmu, slice(None), slice(None)) + xsite].T.copy())
            S.append(float(m.evaluate(U, need_grad=False)[0][0]))
        vx = np.array(vx)
        tau_vx = float(np.nanmax([cl.tauint(vx[:, c, i]) for c in range(vx.shape[1]) for i in range(4)]))
        tau_S = cl.tauint(np.array(S))
        mh = m.mass if m.mass is not None else np.ones(1)
        row = {"kappa": kappa, "t_mass_s": t_mass, "mass_min": float(np.min(mh)), "mass_median": float(np.median(mh)),
               "mass_max": float(np.max(mh)), "tuning": tuning, "eps": eps, "nleap": nleap, "acc_meas": float(np.mean(accm)),
               "s_traj": float(np.median(ts)), "tau_int_vx": tau_vx, "tau_int_S": tau_S, "n_meas": a.n_meas,
               "wall_kappa_s": time.time() - t_k}
        out["per_kappa"].append(row)
        print(json.dumps(row), flush=True)
        if time.time() - t_start > a.max_wall:
            out["stopped"] = "max_wall after kappa %g" % kappa
            break
    out["wall_s"] = time.time() - t_start
    json.dump(out, open(a.out, "w"), indent=1)
    return 0


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest="cmd", required=True)
    sp.add_parser("selftest")
    r = sp.add_parser("run")
    r.add_argument("--go", action="store_true")
    r.add_argument("--action", choices=["wilson", "fit280"], default="wilson")
    r.add_argument("--beta", type=float, default=0.5)
    r.add_argument("--N", type=int, default=16)
    r.add_argument("--n", type=int, default=2)
    r.add_argument("--w", type=float, default=2.0)
    r.add_argument("--kappa", type=float, default=200.0)
    r.add_argument("--R", type=int, default=2)
    r.add_argument("--B", type=int, default=1)
    r.add_argument("--x", default="0,0,0,0,1", help="target coarse link: site,site,site,site,mu")
    r.add_argument("--y", default="0,0,0,0,2", help="moved partner coarse link")
    r.add_argument("--move", choices=["none", "flip", "rot", "small"], default="none")
    r.add_argument("--delta", type=float, default=0.2)
    r.add_argument("--background", choices=["typical", "flat"], default="typical")
    r.add_argument("--npre", type=int, default=50)
    r.add_argument("--nanneal", type=int, default=20)
    r.add_argument("--ntherm", type=int, default=20)
    r.add_argument("--ntraj", type=int, default=200)
    r.add_argument("--eps", type=float, default=0.05)
    r.add_argument("--nleap", type=int, default=10)
    r.add_argument("--seed", type=int, default=1)
    r.add_argument("--bgseed", type=int, default=1000)
    r.add_argument("--pin-mass", action="store_true", help="n = 0: kinetic mass 1 + kappa on the pinned links")
    r.add_argument("--tune-traj", type=int, default=10)
    r.add_argument("--tune-max", type=int, default=6)
    r.add_argument("--max-wall", type=float, default=600.0, help="seconds; the run stops and saves what it has")
    r.add_argument("--out", default="pilot_run.npz")
    tm = sp.add_parser("timing")
    tm.add_argument("--go", action="store_true")
    tm.add_argument("--gpu", action="store_true")
    tm.add_argument("--action", choices=["wilson", "fit280"], default="wilson")
    tm.add_argument("--beta", type=float, default=2.3)
    tm.add_argument("--N", type=int, default=40)
    tm.add_argument("--n", type=int, default=3)
    tm.add_argument("--w", type=float, default=2.0)
    tm.add_argument("--kappa", type=float, default=200.0)
    tm.add_argument("--R", type=int, default=2)
    tm.add_argument("--B", type=int, default=1)
    tm.add_argument("--x", default="0,0,0,0,1")
    tm.add_argument("--npre", type=int, default=200)
    tm.add_argument("--ntraj", type=int, default=100000)
    tm.add_argument("--eps", type=float, default=0.05)
    tm.add_argument("--nleap", type=int, default=10)
    tm.add_argument("--tune-traj", type=int, default=10)
    tm.add_argument("--tune-max", type=int, default=6)
    tm.add_argument("--seed", type=int, default=31)
    tm.add_argument("--bgseed", type=int, default=3000)
    tm.add_argument("--max-wall", type=float, default=1680.0)
    tm.add_argument("--progress", default="timing_progress.jsonl")
    tm.add_argument("--out", default="timing_job.npz")
    tu = sp.add_parser("tune")
    tu.add_argument("--go", action="store_true")
    tu.add_argument("--action", choices=["wilson", "fit280"], default="wilson")
    tu.add_argument("--beta", type=float, default=0.5)
    tu.add_argument("--N", type=int, default=8)
    tu.add_argument("--n", type=int, default=1)
    tu.add_argument("--w", type=float, default=2.0)
    tu.add_argument("--kappas", default="10,20,40")
    tu.add_argument("--precond", action="store_true")
    tu.add_argument("--nprobe", type=int, default=16)
    tu.add_argument("--R", type=int, default=2)
    tu.add_argument("--B", type=int, default=1)
    tu.add_argument("--x", default="0,0,0,0,1")
    tu.add_argument("--npre", type=int, default=100)
    tu.add_argument("--eps", type=float, default=0.05)
    tu.add_argument("--nleap", type=int, default=10)
    tu.add_argument("--tune-traj", type=int, default=10)
    tu.add_argument("--tune-max", type=int, default=6)
    tu.add_argument("--n-meas", type=int, default=40)
    tu.add_argument("--seed", type=int, default=41)
    tu.add_argument("--bgseed", type=int, default=4000)
    tu.add_argument("--max-wall", type=float, default=1500.0)
    tu.add_argument("--out", default="tune.json")
    a = ap.parse_args()
    return {"selftest": selftest, "run": run, "timing": timing, "tune": tune}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
