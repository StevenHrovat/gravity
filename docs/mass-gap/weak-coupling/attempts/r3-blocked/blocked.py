"""Blocked effective action of 4D SU(2) at physical block sizes: the "click" test (round 3, Leg C; PREREG.md in this folder).

A periodic N^4 lattice is simulated at bare coupling beta. SU(2): Wilson action, the fused CUDA kernels of ../../../lattice/gpu/gauge.py
through ../../../lattice/boundary.py (imported, not edited; numpy heat bath with --cpu). Controls U(1) (photon) and Z2: boundary.py's
array code. Every measurement takes each chain's configuration through three steps.

1. Gradient flow (Wilson flow; Luescher, JHEP 08 (2010) 071) in Euler steps of size rho (a stout step, Morningstar and Peardon 2004,
   with the flow's normalisation): on unit quaternions u' = exp(rho X) u, X = -Im(u S), S the sum of the six staples, so that
   du/dt = P_u(A) (A = conj S, P_u the projection on the tangent space of the unit 3-sphere). In the U(1) subgroup this is
   theta' = theta - rho sum_p sin theta_p, the heat equation with unit coefficient: sqrt(8t) is the rms smoothing radius in four
   dimensions. The flow stops exactly at every flow time of the schedule (last step shortened). The plaquette at every step is
   recorded: E = 24 (1 - <(1/2) tr U_p>) (plaquette definition) and the gradient-flow coupling g^2_GF = (128 pi^2 / 9) t^2 E (SU(2)).
2. Blocking: at flow time t = (f b)^2 / 8 (smoothing radius sqrt(8t) = f b lattice units), the coarse link of block size b is the
   product of the b flowed links along the block edge, V(X, mu) = U(s + bX, mu) U(s + bX + mu, mu) ... U(s + bX + (b-1) mu, mu). It is a
   group element, covariant under gauge transformations at the coarse sites (fine transformations inside the edge cancel). Sixteen
   coarse lattices per configuration: origin s in {0, b/2}^4 (one for b = 1). f = 0 is the unsmoothed path product.
3. Schwinger-Dyson sums on the coarse lattice (the inverse Monte Carlo method of Falcioni, Martinelli, Paciello, Parisi and Taglienti
   1986 and of Gonzalez-Arroyo and Okawa 1987, as used on blocked SU(3) configurations by Takaishi 1996; credit for the idea, our own
   derivation and code). For an effective action S = sum_i beta_i F_i and any link, integration by parts with the left-invariant
   vector fields on the group gives sum_i beta_i <grad F_j . grad F_i> = -<Lap F_j> for every basis function j. Recorded per
   configuration: M_ij = <grad F_i . grad F_j> and c_j = -<Lap F_j>, averaged over all coarse links; the fit is M beta = c
   (analyse_blocked.py). Basis, per plaquette p (and rectangle R), with the representation's character over its dimension:
     SU(2): fund (1/2) tr V_p, adj chi_1(V_p) / 3 = ((tr V_p)^2 - 1) / 3, spin3/2 chi_{3/2}(V_p) / 4, rect (1/2) tr V_R (1x2 loops);
     U(1):  q1 cos theta_p, q2 cos 2 theta_p, q3 cos 3 theta_p, rect cos theta_R;
     Z2:    no Lie derivative; per configuration the joint histogram of (sigma_l sum_k s_k, sigma_l sum_j r_j) over coarse links, the
            sufficient statistic of the pseudo-likelihood (Besag) fit of plaq and rect couplings.
   SU(2) formulas, with t_k = (1/2) tr of the k-th plaquette through the link (k = 1..6) and |a_k| = 1 its staple direction:
     grad g(t) = g'(t) P a,  Lap g(t) = g''(t)(1 - t^2) - 3 t g'(t);  the characters are eigenfunctions (eigenvalues -3, -8, -15).

Usage
-----
  python blocked.py run GROUP BETA N BLOCKS FRACS N_THERM N_MEAS SEED OUT.npz [--chains 4] [--every 4] [--n-or 3] [--rho 0.1] [--cpu]
        [--hot] [--gf-tmax T]
        BLOCKS e.g. 6,9,12 (each must divide N, N / b >= 3); FRACS e.g. 0,0.25,0.5 (smoothing radius / block size; Z2: 0 only)
  python blocked.py selftest [--gpu]      staples, rectangles, gauge covariance, flow normalisation, SD fit against known actions
  python blocked.py bench [--cpu] [--N 36] [--chains 4]   timing of sweeps, flow steps and coarse measurements (GPU-time estimate)
Output: OUT.npz, checkpointed every 10 measurements (partial=1 until done).
"""

import argparse
import math
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
LATTICE = os.path.normpath(os.path.join(HERE, "..", "..", "..", "lattice"))
sys.path.insert(0, LATTICE)
import boundary as BD  # noqa: E402  (ours: imported, never edited)

BASIS = {"su2": ("fund", "adj", "spin3/2", "rect"), "u1": ("q1", "q2", "q3", "rect"), "z2": ("plaq", "rect")}
Z2_BINS = (7, 19)  # sigma * sum of 6 plaquette staples in -6..6 (even), of 18 rectangle staples in -18..18 (even)
GF_NORM_SU2 = 128 * np.pi ** 2 / 9  # g^2_GF = GF_NORM t^2 <E> for SU(2) (Luescher 2010: t^2 <E> = 3 (N^2 - 1) g^2 / (128 pi^2))


# ---------------------------------------------------------------------------------------------------------------------------- algebra

class QOps:
    """SU(2) as unit quaternions, component axis FIRST: arrays (4, batch, X0, X1, X2, X3); boundary.qmul's product convention
    (a0 + i a.sigma). Contiguous components keep the GPU array code bandwidth-friendly."""
    group = "su2"
    ax0 = 2

    def __init__(self, xp):
        self.xp = xp
        self.kernel = None
        if xp is not np and os.environ.get("BLOCKED_FUSED", "1") != "0":
            # one fused GPU kernel for the product (about 8 times less memory traffic than the array expression below, which
            # stays the reference: selftest --gpu compares the two paths; BLOCKED_FUSED=0 switches the kernel off)
            self.kernel = xp.ElementwiseKernel(
                "float64 a0, float64 a1, float64 a2, float64 a3, float64 b0, float64 b1, float64 b2, float64 b3",
                "float64 c0, float64 c1, float64 c2, float64 c3",
                """c0 = a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3;
                   c1 = a0 * b1 + b0 * a1 - (a2 * b3 - a3 * b2);
                   c2 = a0 * b2 + b0 * a2 - (a3 * b1 - a1 * b3);
                   c3 = a0 * b3 + b0 * a3 - (a1 * b2 - a2 * b1);""",
                "blocked_qmul")

    def mul(self, a, b):
        if self.kernel is not None and a.shape == b.shape:
            a = self.xp.ascontiguousarray(a)
            b = self.xp.ascontiguousarray(b)
            c = self.xp.empty_like(a)
            self.kernel(a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3], c[0], c[1], c[2], c[3])
            return c
        a0, a1, a2, a3 = a
        b0, b1, b2, b3 = b
        return self.xp.stack([a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3,
                              a0 * b1 + b0 * a1 - (a2 * b3 - a3 * b2),
                              a0 * b2 + b0 * a2 - (a3 * b1 - a1 * b3),
                              a0 * b3 + b0 * a3 - (a1 * b2 - a2 * b1)])

    def dag(self, a):
        return self.xp.concatenate([a[:1], -a[1:]])

    def dot(self, a, b):
        return (a * b).sum(axis=0)


class AOps:
    """U(1) and Z2 as angles, arrays (batch, X0, X1, X2, X3) (boundary.py's layout)."""
    ax0 = 1

    def __init__(self, xp, group="u1"):
        self.xp, self.group = xp, group

    def mul(self, a, b):
        return a + b

    def dag(self, a):
        return -a


def make_ops(group, xp):
    return QOps(xp) if group == "su2" else AOps(xp, group)


def sh(ops, x, mu, s=1):
    """Field at site + s * mu-hat."""
    return ops.xp.roll(x, -s, axis=ops.ax0 + mu)


def shift(ops, x, p):
    for nu, s in enumerate(p):
        if s:
            x = sh(ops, x, nu, s)
    return x


def path(ops, U, mu, steps):
    """Product of links along the path that starts at x + mu-hat (the end of link (x, mu)) and returns to x; steps = [(nu, +-1), ...].
    The closed loop through link (x, mu) is U_mu(x) * path."""
    p = [0, 0, 0, 0]
    p[mu] = 1
    prod = None
    for nu, s in steps:
        if s > 0:
            link = shift(ops, U[nu], p)
            p[nu] += 1
        else:
            p[nu] -= 1
            link = ops.dag(shift(ops, U[nu], p))
        prod = link if prod is None else ops.mul(prod, link)
    assert p == [0, 0, 0, 0], "path does not close"
    return prod


def plaq_steps(mu):
    out = []
    for nu in range(4):
        if nu != mu:
            out.append([(nu, 1), (mu, -1), (nu, -1)])
            out.append([(nu, -1), (mu, -1), (nu, 1)])
    return out


def rect_steps(mu):
    """The 18 1x2 rectangles through link (x, mu): long in mu with the link first (a) or second (b), long in nu (c), nu = +-."""
    out = []
    for nu in range(4):
        if nu == mu:
            continue
        for s in (1, -1):
            out.append([(mu, 1), (nu, s), (mu, -1), (mu, -1), (nu, -s)])
            out.append([(nu, s), (mu, -1), (mu, -1), (nu, -s), (mu, 1)])
            out.append([(nu, s), (nu, s), (mu, -1), (nu, -s), (nu, -s)])
    return out


PLAQ = [plaq_steps(mu) for mu in range(4)]
RECT = [rect_steps(mu) for mu in range(4)]


def qexp(xp, X):
    """exp of the pure-imaginary quaternion X (3, ...) -> unit quaternion (4, ...)."""
    n = xp.sqrt((X * X).sum(axis=0))
    s = xp.where(n > 1e-8, xp.sin(n) / xp.maximum(n, 1e-300), 1.0 - n * n / 6.0)
    return xp.concatenate([xp.cos(n)[None], s[None] * X])


def to_host(x):
    return BD.to_host(x)


# ---------------------------------------------------------------------------------------------------------------------------- flow

def staple_sum_su2(ops, U, mu):
    """Sum S of the six plaquette staples of link (x, mu), as boundary.staple_generic: (1/2) tr(U_mu(x) S_k) is the plaquette."""
    S = None
    for nu in range(4):
        if nu == mu:
            continue
        up = ops.mul(ops.mul(sh(ops, U[nu], mu), ops.dag(sh(ops, U[mu], nu))), ops.dag(U[nu]))
        unm = sh(ops, U[nu], nu, -1)
        dn = ops.mul(ops.mul(ops.dag(sh(ops, unm, mu)), ops.dag(sh(ops, U[mu], nu, -1))), unm)
        S = up + dn if S is None else S + up + dn
    return S


def force_su2(ops, W):
    """Flow force X_mu = -Im(W_mu S_mu) (pure imaginary, (3, ...)) for every direction, and the mean plaquette."""
    X, tr = [], 0.0
    for mu in range(4):
        q = ops.mul(W[mu], staple_sum_su2(ops, W, mu))
        tr = tr + q[0].mean()
        X.append(-q[1:])
    return X, float(tr) / 24.0  # mean over links of <u, A> = 6 <P>, averaged over 4 directions


def renorm(xp, w):
    return w / xp.sqrt((w * w).sum(axis=0, keepdims=True))


def flow_euler_su2(ops, W, eps):
    xp = ops.xp
    X, P = force_su2(ops, W)
    return [renorm(xp, ops.mul(qexp(xp, eps * X[mu]), W[mu])) for mu in range(4)], P


def flow_rk3_su2(ops, W, eps):
    """Luescher's third-order Runge-Kutta step (2010, appendix C); used only to measure the Euler step's error."""
    xp = ops.xp
    Z0, P = force_su2(ops, W)
    Z0 = [eps * z for z in Z0]
    W1 = [ops.mul(qexp(xp, 0.25 * Z0[m]), W[m]) for m in range(4)]
    Z1 = [eps * z for z in force_su2(ops, W1)[0]]
    W2 = [ops.mul(qexp(xp, 8 / 9 * Z1[m] - 17 / 36 * Z0[m]), W1[m]) for m in range(4)]
    Z2 = [eps * z for z in force_su2(ops, W2)[0]]
    W3 = [renorm(xp, ops.mul(qexp(xp, 0.75 * Z2[m] - 8 / 9 * Z1[m] + 17 / 36 * Z0[m]), W2[m])) for m in range(4)]
    return W3, P


def flow_euler_u1(ops, W, eps):
    xp = ops.xp
    new, tr = [], 0.0
    for mu in range(4):
        z = xp.exp(1j * W[mu]) * BD.staple_generic(BD.U1Ops(xp), W, mu)
        tr = tr + z.real.mean()
        th = W[mu] - eps * z.imag
        new.append(xp.remainder(th + np.pi, 2 * np.pi) - np.pi)
    return new, float(tr) / 24.0


# ---------------------------------------------------------------------------------------------------------------------------- blocking

def block(ops, U, b):
    """Coarse links of block size b for the origins s in {0, b//2}^4, stacked into the batch axis: list of 4 arrays
    (lead..., batch * n_origins, Nc, Nc, Nc, Nc). The batch axis of U is kept (usually 1)."""
    xp = ops.xp
    N = U[0].shape[ops.ax0]
    assert N % b == 0, "b must divide N"
    Nc = N // b
    offs = sorted({0, b // 2})
    no = len(offs)
    base = [o + b * np.arange(Nc) for o in offs]
    It = xp.asarray(np.concatenate(base) % N)
    out = []
    for mu in range(4):
        x = U[mu]
        for nu in range(4):
            if nu != mu:
                x = xp.take(x, It, axis=ops.ax0 + nu)
        prod = None
        for k in range(b):
            y = xp.take(x, xp.asarray(np.concatenate([g + k for g in base]) % N), axis=ops.ax0 + mu)
            prod = y if prod is None else ops.mul(prod, y)
        lead = prod.shape[:ops.ax0]
        k0 = len(lead)
        v = prod.reshape(lead + (no, Nc) * 4)  # each spatial axis was (origin, X) in origin-major order
        perm = list(range(k0)) + [k0, k0 + 2, k0 + 4, k0 + 6] + [k0 + 1, k0 + 3, k0 + 5, k0 + 7]
        v = v.transpose(perm).reshape(lead[:-1] + (lead[-1] * no ** 4,) + (Nc,) * 4)
        out.append(xp.ascontiguousarray(v))
    return out


# ---------------------------------------------------------------------------------------------------------------------------- SD sums

def sd_su2(ops, V):
    """Schwinger-Dyson sums on a coarse SU(2) configuration: M (4, 4), c (4), observables (plaq, adj/3, rect), per-link means."""
    xp = ops.xp
    Ms, cs, os_ = [], [], []
    for mu in range(4):
        u = V[mu]
        a = [ops.dag(path(ops, V, mu, st)) for st in PLAQ[mu]]
        R = None
        for st in RECT[mu]:
            r = ops.dag(path(ops, V, mu, st))
            R = r if R is None else R + r
        t = [ops.dot(u, ak) for ak in a]
        A = sum(a)
        uA = sum(t)
        B1 = sum(tk * ak for tk, ak in zip(t, a))
        s2 = sum(tk * tk for tk in t)
        w3 = [6 * tk * tk - 1 for tk in t]
        B3 = sum(wk * ak for wk, ak in zip(w3, a))
        s3 = sum(wk * tk for wk, tk in zip(w3, t))
        uR = ops.dot(u, R)
        g = [A - uA * u, (8.0 / 3.0) * (B1 - s2 * u), B3 - s3 * u, R - uR * u]
        cv = [3 * uA, (8.0 / 3.0) * (4 * s2 - 6), 15 * sum(2 * tk ** 3 - tk for tk in t), 3 * uR]
        Ms.append(xp.stack([ops.dot(g[i], g[j]).mean() for i in range(4) for j in range(4)]))
        cs.append(xp.stack([x.mean() for x in cv]))
        os_.append(xp.stack([uA.mean() / 6, ((4 * s2 - 6) / 18).mean(), uR.mean() / 18]))
    M = to_host(sum(Ms)).reshape(4, 4) / 4
    return M, to_host(sum(cs)) / 4, to_host(sum(os_)) / 4


def sd_u1(ops, V):
    xp = ops.xp
    Ms, cs, os_ = [], [], []
    for mu in range(4):
        th = V[mu]
        c = [th + path(ops, V, mu, st) for st in PLAQ[mu]]
        zr = sum(xp.exp(1j * (th + path(ops, V, mu, st))) for st in RECT[mu])
        g = [-sum(xp.sin(ck) for ck in c), -2 * sum(xp.sin(2 * ck) for ck in c), -3 * sum(xp.sin(3 * ck) for ck in c), -zr.imag]
        cos1 = sum(xp.cos(ck) for ck in c)
        cos2 = sum(xp.cos(2 * ck) for ck in c)
        cv = [cos1, 4 * cos2, 9 * sum(xp.cos(3 * ck) for ck in c), zr.real]
        Ms.append(xp.stack([(g[i] * g[j]).mean() for i in range(4) for j in range(4)]))
        cs.append(xp.stack([x.mean() for x in cv]))
        os_.append(xp.stack([cos1.mean() / 6, cos2.mean() / 6, zr.real.mean() / 18]))
    return to_host(sum(Ms)).reshape(4, 4) / 4, to_host(sum(cs)) / 4, to_host(sum(os_)) / 4


def hist_z2(ops, V):
    """Z2 pseudo-likelihood statistic: joint histogram of (sigma sum_k s_k, sigma sum_j r_j) over coarse links; observables."""
    xp = ops.xp
    H = None
    pl, rc = 0.0, 0.0
    for mu in range(4):
        th = V[mu]
        x = sum(xp.cos(th + path(ops, V, mu, st)) for st in PLAQ[mu])
        y = sum(xp.cos(th + path(ops, V, mu, st)) for st in RECT[mu])
        ix = xp.rint((x + 6) / 2).astype(xp.int64)
        iy = xp.rint((y + 18) / 2).astype(xp.int64)
        h = xp.bincount((ix * Z2_BINS[1] + iy).ravel(), minlength=Z2_BINS[0] * Z2_BINS[1])
        H = h if H is None else H + h
        pl = pl + x.mean() / 6
        rc = rc + y.mean() / 18
    return to_host(H).reshape(Z2_BINS), np.array([float(pl) / 4, 0.0, float(rc) / 4])


# ---------------------------------------------------------------------------------------------------------------------------- schedule

PRIMARY_F = 0.5
NOISE_BETAS = (16.0, 64.0)  # Wilson-type noise kappa(W) ~ exp(beta_n (1/2) tr W) (U(1): exp(beta_n cos)), r3-wp/NOTE.md 3.1


def make_schedule(blocks, fracs, group="su2", noise=True):
    """Measurement points (t, b, f, noise), sorted by flow time t = (f b)^2 / 8. noise = 0: the deterministic block variable;
    noise = beta_n > 0 (SU(2), U(1), primary f only): the same coarse links multiplied by independent Wilson-type noise
    (added after the round-3 review, PREREG.md 'Changes before data')."""
    pts = {((f * b) ** 2 / 8.0, b, f, 0.0) for b in blocks for f in fracs}
    if noise and group != "z2":
        pts |= {((f * b) ** 2 / 8.0, b, f, bn) for b in blocks for f in fracs if abs(f - PRIMARY_F) < 1e-12 for bn in NOISE_BETAS}
    return [(float(t), int(b), float(f), float(n)) for t, b, f, n in sorted(pts)]


def creutz_r0(t):
    """Loop size of the Creutz signal check at flow time t: max(3, ceil(sqrt(8t)))."""
    return max(3, int(math.ceil(math.sqrt(8 * t) - 1e-9)))


def creutz_loops(ops, W, R0):
    """Mean (1/2) tr of the R x T Wilson loops of the (flowed) fine SU(2) field, over all sites and the six planes, for
    (R, T) = (R0-1, R0-1), (R0, R0), (R0, R0-1), (R0-1, R0). Creutz ratio chi = -ln(W[1] W[0] / (W[2] W[3]))."""
    xp = ops.xp
    lines = []
    for mu in range(4):
        cur, d = W[mu], {1: W[mu]}
        for n in range(2, R0 + 1):
            cur = ops.mul(cur, sh(ops, W[mu], mu, n - 1))
            d[n] = cur
        lines.append(d)
    out = []
    for R, T in ((R0 - 1, R0 - 1), (R0, R0), (R0, R0 - 1), (R0 - 1, R0)):
        acc = 0.0
        for mu in range(4):
            for nu in range(mu + 1, 4):
                a = ops.mul(lines[mu][R], sh(ops, lines[nu][T], mu, R))
                b_ = ops.mul(lines[nu][T], sh(ops, lines[mu][R], nu, T))
                acc = acc + ops.dot(a, b_).mean()  # (1/2) tr(a b_^dagger) = <a, b_>
        out.append(float(acc) / 6)
    return np.array(out)


def add_noise(ops, V, beta_n, rng):
    """Multiply every coarse link by an independent draw of the Wilson-type noise kernel (density exp(beta_n (1/2) tr W) against
    Haar for SU(2), exp(beta_n cos w) for U(1)); a kernel continuous and bounded below, as r3-wp's noise lemma needs."""
    xp = ops.xp
    out = []
    for v in V:
        if ops.group == "su2":
            n = int(np.prod(v.shape[1:]))
            x0 = BD.kp_x0(np.full((1, n), beta_n), BD.Draws(np, int(rng.integers(1 << 62)), 1))[0]
            d = rng.normal(size=(3, n))
            d /= np.linalg.norm(d, axis=0, keepdims=True)
            w = np.concatenate([x0[None], np.sqrt(np.maximum(0.0, 1 - x0 * x0))[None] * d]).reshape(v.shape)
            out.append(ops.mul(xp.asarray(w), v))
        else:
            n = int(np.prod(v.shape))
            ang = BD.vonmises(np, np.full((1, n), beta_n), BD.Draws(np, int(rng.integers(1 << 62)), 1))[0].reshape(v.shape)
            out.append(v + xp.asarray(ang))
    return out


def measure_config(group, ops, U, schedule, rho, t_extra=0.0, rng=None, creutz=None):
    """Flow one configuration through the schedule (and on to t_extra, recording only the plaquette); returns per point (M, c, obs)
    or (hist, obs), and the flow record (t, plaq) taken at the start of every flow step. With creutz = [] (SU(2)), the Creutz
    signal-check loops of the flowed fine field at each point's flow time are appended to it, one row per point."""
    rng = np.random.default_rng(0) if rng is None else rng
    schedule = [tuple(p) + (0.0,) * (4 - len(p)) for p in schedule]
    W = U
    tcur = 0.0
    flow = []
    res = [None] * len(schedule)
    cz = [None] * len(schedule)
    step = flow_euler_su2 if group == "su2" else flow_euler_u1
    targets = sorted({p[0] for p in schedule} | ({t_extra} if group != "z2" and t_extra > 0 else set()))
    for t in targets:
        while tcur < t - 1e-12:
            nxt = (math.floor(tcur / rho + 1e-9) + 1) * rho  # steps stay aligned to multiples of rho (the GF table's grid)
            eps = min(nxt - tcur, t - tcur)
            W, P = step(ops, W, eps)
            flow.append((tcur, P))
            tcur += eps
        idx = [i for i, p in enumerate(schedule) if abs(p[0] - t) < 1e-12]
        if idx and creutz is not None and group == "su2":
            loops = creutz_loops(ops, W, creutz_r0(t))
            for i in idx:
                cz[i] = loops
        for b in sorted({schedule[i][1] for i in idx}):
            V = block(ops, W, b)
            for i in idx:
                if schedule[i][1] != b:
                    continue
                Vi = V if schedule[i][3] == 0 else add_noise(ops, V, schedule[i][3], rng)
                res[i] = sd_su2(ops, Vi) if group == "su2" else (sd_u1(ops, Vi) if group == "u1" else hist_z2(ops, Vi))
    if creutz is not None:
        creutz.extend(cz)
    return res, flow


# ---------------------------------------------------------------------------------------------------------------------------- generator

class PeriodicBox:
    """What boundary.py's updaters need from a Box, for a periodic N^4 lattice with every link dynamic."""

    def __init__(self, N):
        assert N % 2 == 0, "N must be even (checkerboard)"
        self.N, self.ell = N, N
        self.dims = (N,) * 4
        self.dyn = [np.ones(self.dims, bool) for _ in range(4)]
        par = np.indices(self.dims).sum(axis=0) % 2
        self.parity = [par == 0, par == 1]


def periodic_gpu_su2():
    class PeriodicGPUSU2(BD.GPUSU2):
        """boundary.GPUSU2 with nothing frozen: no copy of the links, no restores (saves memory on large lattices)."""

        def set_dynamic(self, dyn):
            self.dyn = dyn

        def restore(self, mu):
            pass
    return PeriodicGPUSU2


def cold(group, box, B, hot=False, seed=0):
    """Start configuration: unit links, or (hot, U(1) and Z2 only) uniformly random angles."""
    if hot and group != "su2":
        rng = np.random.default_rng(20_000 + seed)
        if group == "z2":
            return [np.pi * rng.integers(0, 2, size=(B,) + box.dims).astype(float) for _ in range(4)]
        return [rng.uniform(-np.pi, np.pi, size=(B,) + box.dims) for _ in range(4)]
    if group == "su2":
        q = np.zeros((B,) + box.dims + (4,))
        q[..., 0] = 1.0
        return [q.copy() for _ in range(4)]
    return [np.zeros((B,) + box.dims) for _ in range(4)]


def make_updater(group, box, beta, B, seed, gpu, hot=False):
    U0 = cold(group, box, B, hot, seed)
    if group == "su2":
        return periodic_gpu_su2()(box, beta, U0, seed) if gpu else BD.CPUSU2(box, beta, U0, seed)
    return BD.U1Updater(BD.get_xp(gpu), box, beta, U0, seed, z2=(group == "z2"))


def chain_config(group, xp, links, c):
    """Chain c of the updater's links in this script's layout (batch 1)."""
    if group == "su2":
        return [xp.ascontiguousarray(xp.moveaxis(xp.asarray(L[c:c + 1]), -1, 0)) for L in links]
    return [xp.array(L[c:c + 1]) for L in links]


# ---------------------------------------------------------------------------------------------------------------------------- run

def run(a):
    gpu = not a.cpu
    xp = BD.get_xp(gpu)
    blocks = [int(x) for x in a.blocks.split(",")]
    fracs = [float(x) for x in a.fracs.split(",")] if a.group != "z2" else [0.0]
    for b in blocks:
        if a.N % b or a.N // b < 3:
            raise SystemExit(f"block {b}: must divide N = {a.N} with N / b >= 3")
    schedule = make_schedule(blocks, fracs, a.group)
    box = PeriodicBox(a.N)
    B = a.chains
    upd = make_updater(a.group, box, a.beta, B, a.seed, gpu, a.hot)
    ops = make_ops(a.group, xp)
    t0 = time.time()
    for _ in range(a.n_therm):
        upd.sweep(a.n_or)
    print(f"{a.group} beta={a.beta} N={a.N} thermalised ({a.n_therm} sweeps) t={time.time() - t0:.0f}s; schedule (t, b, f, noise): "
          f"{[(round(t, 4), b, f, n) for t, b, f, n in schedule]}", flush=True)
    rec = {"M": [], "c": [], "obs": [], "hist": [], "flow_plaq": [], "creutz": []}
    flow_t = None

    def save(m, partial):
        out = dict(group=a.group, beta=a.beta, N=a.N, blocks=np.array(blocks), fracs=np.array(fracs), schedule=np.array(schedule),
                   rho=a.rho, gf_tmax=a.gf_tmax, chains=B, n_therm=a.n_therm, hot=int(a.hot), every=a.every, n_or=a.n_or, seed=a.seed, backend="gpu" if gpu else "cpu",
                   basis=np.array(BASIS[a.group]), seconds=time.time() - t0, partial=int(partial), n_done=m,
                   obs=np.array(rec["obs"]), noise_betas=np.array(NOISE_BETAS), primary_f=PRIMARY_F)
        if a.group == "su2":
            out["creutz"] = np.array(rec["creutz"])
            out["creutz_r0"] = np.array([creutz_r0(p[0]) for p in schedule])
        if a.group == "z2":
            out["hist"] = np.array(rec["hist"])
        else:
            out["M"], out["c"] = np.array(rec["M"]), np.array(rec["c"])
            out["flow_t"], out["flow_plaq"] = np.array(flow_t if flow_t is not None else []), np.array(rec["flow_plaq"])
        np.savez(a.out, **out)

    for m in range(a.n_meas):
        for _ in range(a.every):
            upd.sweep(a.n_or)
        links = upd.links()
        per = {k: [] for k in rec}
        for c in range(B):
            cz = [] if a.group == "su2" else None
            res, flow = measure_config(a.group, ops, chain_config(a.group, xp, links, c), schedule, a.rho, a.gf_tmax,
                                       rng=np.random.default_rng((a.seed, m, c)), creutz=cz)
            if cz is not None:
                per["creutz"].append(cz)
            if a.group == "z2":
                per["hist"].append([r[0] for r in res])
            else:
                per["M"].append([r[0] for r in res])
                per["c"].append([r[1] for r in res])
                per["flow_plaq"].append([p for _, p in flow])
                flow_t = [t for t, _ in flow]
            per["obs"].append([r[-1] for r in res])
        for k, v in per.items():
            if v:
                rec[k].append(v)
        del links
        if m % 10 == 9 or m == 0:
            save(m + 1, True)
            o = np.array(rec["obs"][-1])
            print(f"{a.group} beta={a.beta} N={a.N} meas {m + 1}/{a.n_meas} t={time.time() - t0:.0f}s coarse plaq per point "
                  f"{np.round(o[:, :, 0].mean(axis=0), 4).tolist()}", flush=True)
    save(a.n_meas, False)
    print(f"done {a.out} in {time.time() - t0:.0f}s", flush=True)
    return 0


# ---------------------------------------------------------------------------------------------------------------------------- tests

def metropolis(group, couplings, U, n_sweeps, rng, hits=4, eps=0.6):
    """Metropolis for a plaquette action with several representations (test only): SU(2) beta_F (1/2) tr + beta_A chi_1 / 3 +
    beta_T chi_{3/2} / 4; U(1) sum_k beta_k cos(k theta_p). Checkerboard (direction, parity): exact for plaquette-only actions.
    U: configuration in this script's layout (any batch); returns (U, acceptance)."""
    ops = make_ops(group, np)
    box = PeriodicBox(U[0].shape[-1])
    cpl = list(couplings) + [0.0] * (3 - len(couplings))
    B = U[0].shape[ops.ax0 - 1]

    def local(u, a):
        if group == "su2":
            t = [ops.dot(u, ak) for ak in a]
            return sum(cpl[0] * tk + cpl[1] * (4 * tk * tk - 1) / 3 + cpl[2] * (2 * tk ** 3 - tk) for tk in t)
        return sum(sum(cpl[k] * np.cos((k + 1) * (u + ak)) for k in range(3)) for ak in a)

    acc, tot = 0, 0
    for _ in range(n_sweeps):
        for mu in range(4):
            for p in (0, 1):
                m = box.parity[p][None]
                a = [path(ops, U, mu, st) for st in PLAQ[mu]]
                if group == "su2":
                    a = [ops.dag(x) for x in a]
                for _ in range(hits):
                    u = U[mu]
                    if group == "su2":
                        new = renorm(np, ops.mul(qexp(np, eps * rng.normal(size=(3,) + u.shape[1:])), u))
                    else:
                        new = u + 1.5 * eps * rng.normal(size=u.shape)
                    dS = local(new, a) - local(u, a)
                    okm = (np.log(rng.random(size=dS.shape)) < dS) & m
                    U[mu] = np.where(okm[None], new, u) if group == "su2" else np.where(okm, new, u)
                    acc += int(okm.sum())
                    tot += int(m.sum()) * B
    return U, acc / max(tot, 1)


def fit(M, c, S):
    S = list(S)
    return np.linalg.solve(M[np.ix_(S, S)], c[S])


def sd_ensemble(group, configs, b=1):
    """Mean SD sums over a list of configurations (each a list of 4 arrays in this script's layout), at block size b without flow."""
    ops = make_ops(group, np)
    Ms, cs = [], []
    for U in configs:
        V = block(ops, U, b) if b > 1 else U
        M, c, _ = sd_su2(ops, V) if group == "su2" else sd_u1(ops, V)
        Ms.append(M)
        cs.append(c)
    return np.array(Ms), np.array(cs)


def jk_fit(Ms, cs, S, nblk=10):
    """Fit with jackknife errors over consecutive blocks of configurations."""
    n = len(Ms)
    full = fit(Ms.mean(0), cs.mean(0), S)
    idx = np.array_split(np.arange(n), nblk)
    jk = np.array([fit(np.delete(Ms, i, 0).mean(0), np.delete(cs, i, 0).mean(0), S) for i in idx])
    err = np.sqrt((nblk - 1) / nblk * ((jk - jk.mean(0)) ** 2).sum(0))
    return full, err


def selftest(a):
    gpu = a.gpu
    ok = True

    def report(name, good, detail):
        nonlocal ok
        ok &= bool(good)
        print(f"{'PASS' if good else 'FAIL'}  {name}: {detail}", flush=True)

    rng = np.random.default_rng(11)
    qo, ao = QOps(np), AOps(np)

    def rand_su2(N, B=1):
        return [renorm(np, rng.normal(size=(4, B) + (N,) * 4)) for _ in range(4)]

    # 1. staple sum equals boundary.staple_generic (independent layout and code), and the path staples
    U = rand_su2(4)
    Ulast = [np.moveaxis(u, 0, -1) for u in U]
    d1 = max(np.abs(np.moveaxis(BD.staple_generic(BD.SU2Ops(np), Ulast, mu), -1, 0) - staple_sum_su2(qo, U, mu)).max() for mu in range(4))
    d2 = max(np.abs(sum(path(qo, U, mu, st) for st in PLAQ[mu]) - staple_sum_su2(qo, U, mu)).max() for mu in range(4))
    report("staples: component-first sum = boundary.staple_generic; path staples = sum", max(d1, d2) < 1e-12, f"{d1:.1e}, {d2:.1e}")

    # 2. rectangles: independent direct loops (boundary.qmul, last-axis layout); sum rule and exact linear response at one link
    def rect_total(Ul):
        tot = 0.0
        q = lambda a, b: BD.qmul(a, b)  # noqa: E731
        dg = lambda a: a * np.array([1, -1, -1, -1])  # noqa: E731
        r = lambda x, mu, s=1: np.roll(x, -s, axis=1 + mu)  # noqa: E731
        for mu in range(4):
            for nu in range(4):
                if nu == mu:
                    continue
                loop = q(q(q(q(q(Ul[mu], r(Ul[mu], mu)), r(Ul[nu], mu, 2)), dg(r(r(Ul[mu], mu), nu))), dg(r(Ul[mu], nu))), dg(Ul[nu]))
                tot += loop[..., 0].sum()
        return tot

    def plaq_total(Ul):
        tot = 0.0
        q, dg = BD.qmul, (lambda a: a * np.array([1, -1, -1, -1]))
        for mu in range(4):
            for nu in range(mu + 1, 4):
                loop = q(q(q(Ul[mu], np.roll(Ul[nu], -1, axis=1 + mu)), dg(np.roll(Ul[mu], -1, axis=1 + nu))), dg(Ul[nu]))
                tot += loop[..., 0].sum()
        return tot

    Rsum = sum(qo.dot(U[mu], qo.dag(sum(path(qo, U, mu, st) for st in RECT[mu]))).sum() for mu in range(4))
    T0 = rect_total(Ulast)
    report("rectangles: sum over links of <u, R> = 6 x sum of (1/2) tr over all 1x2 loops", abs(Rsum - 6 * T0) < 1e-9,
           f"{Rsum:.6f} vs 6 x {T0:.6f}")
    errs = []
    for trial in range(6):
        mu = trial % 4
        x0 = tuple(rng.integers(0, 4, size=4))
        w = rng.normal(size=4)
        w /= np.linalg.norm(w)
        Rl = qo.dag(sum(path(qo, U, mu, st) for st in RECT[mu]))[(slice(None), 0) + x0]
        Al = qo.dag(staple_sum_su2(qo, U, mu))[(slice(None), 0) + x0]
        U2 = [u.copy() for u in U]
        U2[mu][(slice(None), 0) + x0] = w
        U2l = [np.moveaxis(u, 0, -1) for u in U2]
        errs.append(abs(rect_total(U2l) - T0 - np.dot(w - U[mu][(slice(None), 0) + x0], Rl)))
        errs.append(abs(plaq_total(U2l) - plaq_total(Ulast) - np.dot(w - U[mu][(slice(None), 0) + x0], Al)))
    report("staples are exact derivatives: changing one link changes the loop totals by <w - u, staple sum>", max(errs) < 1e-10,
           f"max error {max(errs):.1e} (6 links, plaquettes and rectangles)")

    # 3. gauge covariance of flow + blocking + SD sums (SU(2) and U(1)); a random fine gauge transformation
    N = 6
    U = rand_su2(N)
    g = renorm(np, rng.normal(size=(4, 1) + (N,) * 4))
    Ug = [qo.mul(qo.mul(g, U[mu]), qo.dag(sh(qo, g, mu))) for mu in range(4)]
    sched = make_schedule([2], [0.0, 0.5], noise=False)  # the noisy variant is covariant in distribution only
    r1, f1 = measure_config("su2", qo, U, sched, 0.1)
    r2, f2 = measure_config("su2", qo, Ug, sched, 0.1)
    dm = max(max(np.abs(x - y).max() for x, y in zip(p1, p2)) for p1, p2 in zip(r1, r2))
    df = max(abs(x[1] - y[1]) for x, y in zip(f1, f2))
    report("SU(2) gauge covariance: flow, blocking (b = 2, f = 0 and 1/2) and SD sums invariant", max(dm, df) < 1e-10, f"{dm:.1e}, {df:.1e}")
    th = [rng.uniform(-np.pi, np.pi, size=(1,) + (N,) * 4) for _ in range(4)]
    gu = rng.uniform(-np.pi, np.pi, size=(1,) + (N,) * 4)
    thg = [th[mu] + gu - sh(ao, gu, mu) for mu in range(4)]
    r1, _ = measure_config("u1", ao, th, sched, 0.1)
    r2, _ = measure_config("u1", ao, thg, sched, 0.1)
    dm = max(max(np.abs(x - y).max() for x, y in zip(p1, p2)) for p1, p2 in zip(r1, r2))
    report("U(1) gauge covariance: flow, blocking and SD sums invariant", dm < 1e-10, f"{dm:.1e}")

    # 4. flow normalisation: SU(2) flow of a U(1)-subgroup configuration = U(1) flow theta' = theta - rho sum sin theta_p
    al = [0.4 * rng.normal(size=(1,) + (N,) * 4) for _ in range(4)]
    Ue = [np.stack([np.cos(x), 0 * x, 0 * x, np.sin(x)]) for x in al]
    We, Pe = flow_euler_su2(qo, Ue, 0.1)
    Wa, Pa = flow_euler_u1(ao, al, 0.1)
    d = max(np.abs(np.angle(np.exp(1j * (np.arctan2(We[mu][3], We[mu][0]) - Wa[mu])))).max() for mu in range(4))
    report("flow normalisation: SU(2) Euler step on a U(1)-subgroup field = U(1) heat-equation step (unit coefficient)",
           d < 1e-12 and abs(Pe - Pa) < 1e-12, f"angle difference {d:.1e}, plaquette {Pe:.6f} vs {Pa:.6f}")

    # 4b. (after the round-3 review) rectangles on a 3^4 torus, where wrap-around could merge links: sum rule and exact response
    U3 = rand_su2(3)
    U3l = [np.moveaxis(u, 0, -1) for u in U3]
    R3 = sum(qo.dot(U3[mu], qo.dag(sum(path(qo, U3, mu, st) for st in RECT[mu]))).sum() for mu in range(4))
    T3 = rect_total(U3l)
    errs3 = []
    for trial in range(8):
        mu = trial % 4
        x0 = tuple(rng.integers(0, 3, size=4))
        w = rng.normal(size=4)
        w /= np.linalg.norm(w)
        Rl = qo.dag(sum(path(qo, U3, mu, st) for st in RECT[mu]))[(slice(None), 0) + x0]
        U2 = [u.copy() for u in U3]
        U2[mu][(slice(None), 0) + x0] = w
        errs3.append(abs(rect_total([np.moveaxis(u, 0, -1) for u in U2]) - T3 - np.dot(w - U3[mu][(slice(None), 0) + x0], Rl)))
    report("rectangles on a 3^4 torus (wrap-around): sum rule and exact one-link response", abs(R3 - 6 * T3) < 1e-9 and max(errs3) < 1e-10,
           f"sum {R3:.6f} vs 6 x {T3:.6f}; response error {max(errs3):.1e}")

    # 4c. Creutz loops: gauge invariant, and W(2, 2) of the fine field = the coarse plaquette at b = 2 (all 16 origins = all sites)
    U = rand_su2(6)
    g = renorm(np, rng.normal(size=(4, 1) + (6,) * 4))
    Ug = [qo.mul(qo.mul(g, U[mu]), qo.dag(sh(qo, g, mu))) for mu in range(4)]
    c1, c2 = creutz_loops(qo, U, 3), creutz_loops(qo, Ug, 3)
    plaq_b2 = sd_su2(qo, block(qo, U, 2))[2][0]
    report("Creutz loops: gauge invariant; W(2,2) = coarse plaquette at b = 2", np.abs(c1 - c2).max() < 1e-12 and abs(c1[0] - plaq_b2) < 1e-12,
           f"{np.abs(c1 - c2).max():.1e}; {c1[0]:.6f} vs {plaq_b2:.6f}")

    # 4d. noise kernels: mean (1/2) tr W = I_2/I_1 (SU(2)), mean cos w = I_1/I_0 (U(1)), at beta_n = 16 (exact Bessel ratios)
    from scipy.special import iv
    rngn = np.random.default_rng(3)
    V1 = [np.stack([np.ones((1, 40, 40)), 0 * np.ones((1, 40, 40)), 0 * np.ones((1, 40, 40)), 0 * np.ones((1, 40, 40))])] * 4
    Wn = add_noise(qo, V1, 16.0, rngn)
    m_su2 = np.mean([w[0].mean() for w in Wn])
    Va = [np.zeros((1, 40, 40))] * 4
    Wa = add_noise(ao, Va, 16.0, rngn)
    m_u1 = np.mean([np.cos(w).mean() for w in Wa])
    e1, e2 = iv(2, 16) / iv(1, 16), iv(1, 16) / iv(0, 16)
    report("noise kernels at beta_n = 16: SU(2) <(1/2) tr W> = I2/I1, U(1) <cos w> = I1/I0 (6400 draws each)",
           abs(m_su2 - e1) < 0.006 and abs(m_u1 - e2) < 0.006, f"{m_su2:.4f} vs {e1:.4f}; {m_u1:.4f} vs {e2:.4f}")

    # 5. SD fit at b = 1 on Wilson configurations from boundary.py's own heat bath recovers the bare coupling
    box = PeriodicBox(6)
    cfgs = {"su2": [], "u1": []}
    for grp, beta in (("su2", 2.3), ("u1", 1.1)):
        upd = make_updater(grp, box, beta, 4, 7, False)
        for _ in range(100):
            upd.sweep(3)
        for _ in range(30):
            for _ in range(4):  # 4 sweeps between configurations (2 left visible autocorrelation in the four-coupling fit)
                upd.sweep(3)
            L = upd.links()
            cfgs[grp] += [chain_config(grp, np, L, c) for c in range(4)]
        Ms, cs = sd_ensemble(grp, cfgs[grp])
        b2, e2 = jk_fit(Ms, cs, [0, 1])
        b4, e4 = jk_fit(Ms, cs, [0, 1, 2, 3])
        good = abs(b2[0] - beta) < max(4 * e2[0], 0.02 * beta) and abs(b2[1]) < max(4 * e2[1], 0.02)
        report(f"{grp} SD fit, b = 1, Wilson beta = {beta} (boundary.py heat bath, 6^4, 120 configs)", good,
               f"two couplings {np.round(b2, 4)} +- {np.round(e2, 4)}; four {np.round(b4, 3)} +- {np.round(e4, 3)}")
    # Z2: pseudo-likelihood at b = 1
    for beta in (0.3, 0.6):
        upd = make_updater("z2", box, beta, 4, 9, False)
        for _ in range(100):
            upd.sweep(3)
        H = 0
        for _ in range(30):
            upd.sweep(3)
            L = upd.links()
            for c in range(4):
                H = H + hist_z2(ao, chain_config("z2", np, L, c))[0]
        sys.path.insert(0, HERE)
        from analyse_blocked import z2_fit
        bz = z2_fit(H, [0])
        bz2 = z2_fit(H, [0, 1])
        report(f"z2 pseudo-likelihood fit, b = 1, beta = {beta}", abs(bz[0] - beta) < 0.03, f"plaq {bz[0]:.4f}; with rect {np.round(bz2, 4)}")

    # 6. mixed actions with known adjoint / charge-2 couplings (Metropolis, independent of boundary.py), recovered by the SD fit
    for grp, cpl in (("su2", (1.0, 0.8)), ("u1", (0.6, 0.4))):
        ops = make_ops(grp, np)
        rngm = np.random.default_rng(21)
        Uc = cold(grp, PeriodicBox(4), 4)
        if grp == "su2":
            Uc = [np.ascontiguousarray(np.moveaxis(u, -1, 0)) for u in Uc]
        Uc, acc = metropolis(grp, cpl, Uc, 150, rngm)
        Ms, cs = [], []
        for s_ in range(60):
            Uc, acc = metropolis(grp, cpl, Uc, 3, rngm)
            for c in range(4):
                V = [u[:, c:c + 1] if grp == "su2" else u[c:c + 1] for u in Uc]
                M, cc, _ = sd_su2(ops, V) if grp == "su2" else sd_u1(ops, V)
                Ms.append(M)
                cs.append(cc)
        bb, ee = jk_fit(np.array(Ms), np.array(cs), [0, 1])
        good = all(abs(bb[i] - cpl[i]) < max(4 * ee[i], 0.05) for i in range(2))
        report(f"{grp} SD fit recovers a mixed action {cpl} (Metropolis, 4^4, 240 configs, acceptance {acc:.2f})", good,
               f"{np.round(bb, 4)} +- {np.round(ee, 4)}")

    # 7. Euler step error of the flow (rho = 0.1) against RK3 (eps = 0.02), SU(2) beta = 2.3 configuration
    U = cfgs["su2"][-1]
    W1, W2 = U, U
    for _ in range(10):
        W1, _ = flow_euler_su2(qo, W1, 0.1)
    for _ in range(50):
        W2, _ = flow_rk3_su2(qo, W2, 0.02)
    P1, P2 = force_su2(qo, W1)[1], force_su2(qo, W2)[1]
    rel = abs((1 - P1) - (1 - P2)) / (1 - P2)
    report("Euler flow (rho = 0.1) against RK3 at t = 1: relative difference of E(t) (indicative, part of the blocking definition)",
           rel < 0.10, f"E_euler/E_rk3 - 1 = {(1 - P1) / (1 - P2) - 1:+.4f} on one 6^4 configuration (alarm at 10 %; over 8 configurations "
           f"on 8^4 the bias is +3.2 +- 0.3 % at t = 1 and +2.8 +- 0.4 % at t = 2: a stated systematic of alpha_GF); t^2 E = {24 * (1 - P2):.4f}")

    if gpu:
        import cupy as cp
        qg = QOps(cp)
        if qg.kernel is not None:
            x = cp.asarray(renorm(np, rng.normal(size=(4, 2, 5, 5, 5, 5))))
            y = cp.asarray(renorm(np, rng.normal(size=(4, 2, 5, 5, 5, 5))))
            ref = qo.mul(cp.asnumpy(x), cp.asnumpy(y))
            d = float(np.abs(cp.asnumpy(qg.mul(x, y)) - ref).max())
            report("fused GPU quaternion product = numpy product", d < 1e-14, f"{d:.1e}")
        print(f"GPU path: {'fused quaternion kernel' if qg.kernel is not None else 'array code (BLOCKED_FUSED=0)'}", flush=True)
        U = cfgs["su2"][-1]
        sched = make_schedule([2, 3], [0.0, 0.25, 0.5])
        czc, czg = [], []
        rc, fc = measure_config("su2", qo, U, sched, 0.1, creutz=czc)
        rg, fg = measure_config("su2", QOps(cp), [cp.asarray(u) for u in U], sched, 0.1, creutz=czg)
        dm = max(max(np.abs(np.asarray(x) - np.asarray(y)).max() for x, y in zip(p1, p2)) for p1, p2 in zip(rc, rg))
        dz = max(float(np.abs(np.asarray(x) - np.asarray(y)).max()) for x, y in zip(czc, czg))
        report("GPU = CPU: SU(2) flow, blocking, noisy variants, SD sums, Creutz loops on one configuration", max(dm, dz) < 1e-9,
               f"{dm:.1e}, {dz:.1e}")
        th = cfgs["u1"][-1]
        rc, _ = measure_config("u1", ao, th, sched, 0.1)
        rg, _ = measure_config("u1", AOps(cp), [cp.asarray(u) for u in th], sched, 0.1)
        dm = max(max(np.abs(np.asarray(x) - np.asarray(y)).max() for x, y in zip(p1, p2)) for p1, p2 in zip(rc, rg))
        report("GPU = CPU: U(1) flow, blocking, SD sums", dm < 1e-9, f"{dm:.1e}")
        # the periodic GPU generator: plaquette at beta = 2.3 on 8^4 against the CPU heat bath (indicative)
        upd = make_updater("su2", PeriodicBox(8), 2.3, 4, 3, True)
        for _ in range(200):
            upd.sweep(3)
        P = []
        for _ in range(50):
            upd.sweep(3)
            P.append(float(np.mean(upd.g.plaquette())))
        report("GPU periodic generator: plaquette at beta = 2.3 (reference 0.6023)", abs(np.mean(P) - 0.6023) < 0.003, f"{np.mean(P):.4f}")
    print("SELFTEST", "OK" if ok else "FAILED")
    return 0 if ok else 1


# ---------------------------------------------------------------------------------------------------------------------------- bench

def bench(a):
    """Timing per chain-configuration: sweeps (generator), flow steps, coarse measurement per block size; prints the projection."""
    gpu = not a.cpu
    xp = BD.get_xp(gpu)
    sync = (lambda: xp.cuda.Device().synchronize()) if gpu else (lambda: None)
    N, B = a.N, a.chains
    box = PeriodicBox(N)
    out = {}
    for grp, beta in (("su2", 2.3), ("u1", 1.1), ("z2", 0.6)):
        upd = make_updater(grp, box, beta, B, 1, gpu)
        ops = make_ops(grp, xp)
        upd.sweep(3)
        sync()
        t = time.time()
        for _ in range(2):
            upd.sweep(3)
        sync()
        ts = (time.time() - t) / 2 / B
        cfg = chain_config(grp, xp, upd.links(), 0)
        tf = 0.0
        if grp != "z2":
            step = flow_euler_su2 if grp == "su2" else flow_euler_u1
            W, _ = step(ops, cfg, 0.1)
            sync()
            t = time.time()
            for _ in range(3):
                W, _ = step(ops, W, 0.1)
            sync()
            tf = (time.time() - t) / 3
        tb = {}
        for b in [x for x in (6, 9, 12) if N % x == 0 and N // x >= 3] or [N // 3]:
            t = time.time()
            V = block(ops, cfg, b)
            r = sd_su2(ops, V) if grp == "su2" else (sd_u1(ops, V) if grp == "u1" else hist_z2(ops, V))
            sync()
            tb[b] = time.time() - t
        out[grp] = (ts, tf, tb)
        print(f"{grp} N={N} chains={B}: sweep per chain {ts:.3f} s; flow step per config {tf:.3f} s; coarse measurement per point "
              f"{ {k: round(v, 3) for k, v in tb.items()} } s", flush=True)
        del upd, cfg
    if gpu:
        print(f"GPU memory pool in use ~{xp.get_default_memory_pool().used_bytes() / 2**30:.2f} GiB")
    # projection of the pre-registered plan (PLAN) from these timings; sweep and flow costs scaled by volume if N differs from the
    # plan's N (bandwidth-bound array code: proportional to the volume once the GPU is saturated; small N underestimates nothing)
    total = 0.0
    for (grp, beta, Np, blocks, fracs, therm, meas, ch, every, hot, gfmax, seed) in PLAN + PLAN_ADDENDUM:
        ts, tf, tb = out[grp]
        ts, tf = ts * (Np / N) ** 4, tf * (Np / N) ** 4
        sched = make_schedule([int(x) for x in blocks.split(",")], [float(x) for x in fracs.split(",")] if grp != "z2" else [0.0], grp)
        steps = count_flow_steps(sched, 0.1, gfmax) if grp != "z2" else 0
        tm = sum(tb.get(p[1], max(tb.values())) for p in sched)
        sec = therm * ch * ts + meas * ch * (every * ts + steps * tf + tm)
        total += sec
        print(f"  plan {grp} beta={beta} N={Np}: {steps} flow steps per config, about {sec / 60:.0f} min")
    print(f"PROJECTED TOTAL for the plan: {total / 3600:.2f} h (excluding selftest and this bench, about 5 min)")
    return out


def count_flow_steps(schedule, rho, t_extra=0.0):
    tcur, n = 0.0, 0
    for t in sorted({p[0] for p in schedule} | ({t_extra} if t_extra > 0 else set())):
        while tcur < t - 1e-12:
            nxt = (math.floor(tcur / rho + 1e-9) + 1) * rho
            tcur += min(nxt - tcur, t - tcur)
            n += 1
    return n


# The pre-registered GPU plan (PREREG.md; queue_blocked_gpu.ps1 runs exactly these, in this order):
# (group, beta, N, blocks, fracs, n_therm, n_meas, chains, every, hot start, gf_tmax, seed)
PLAN = [
    ("u1", 1.1, 36, "6,9,12", "0,0.25,0.5", 200, 80, 4, 4, False, 0.0, 3101),     # photon control (gate)
    ("su2", 2.3, 36, "6,9,12", "0,0.25,0.5", 200, 80, 4, 4, False, 10.125, 3102),  # L sqrt(sigma) = 2.10, 3.15, 4.20; GF to sqrt(8t) = 9
    ("z2", 0.6, 36, "6,9,12", "0", 200, 80, 4, 4, False, 0.0, 3103),              # deconfined Z2 control
    ("u1", 0.9, 36, "6,9,12", "0,0.25,0.5", 200, 80, 4, 4, True, 0.0, 3104),       # confined U(1), positive control
    ("z2", 0.3, 36, "6,9,12", "0", 200, 80, 4, 4, True, 0.0, 3105),               # confined Z2, positive control
    ("su2", 2.4, 36, "6,9,12", "0,0.25,0.5", 200, 80, 4, 4, False, 0.0, 3106),     # L sqrt(sigma) = 1.55, 2.32, 3.10 (scaling)
]
# Added after the round-3 review (PREREG.md 'Changes before data'); queue_blocked_gpu_addendum.ps1 runs these after the main queue:
PLAN_ADDENDUM = [
    ("u1", 1.3, 36, "6,9,12", "0,0.25,0.5", 200, 80, 4, 4, False, 0.0, 3107),     # second Coulomb beta for the photon gate
    ("su2", 2.3, 24, "6,8", "0,0.25,0.5", 200, 80, 4, 4, False, 0.0, 3108),       # coarse-volume check: b = 6 on 4^4 (vs 6^4)
]


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("group", choices=("su2", "u1", "z2"))
    r.add_argument("beta", type=float)
    r.add_argument("N", type=int)
    r.add_argument("blocks")
    r.add_argument("fracs")
    r.add_argument("n_therm", type=int)
    r.add_argument("n_meas", type=int)
    r.add_argument("seed", type=int)
    r.add_argument("out")
    r.add_argument("--chains", type=int, default=4)
    r.add_argument("--every", type=int, default=4)
    r.add_argument("--n-or", type=int, default=3)
    r.add_argument("--rho", type=float, default=0.1)
    r.add_argument("--cpu", action="store_true")
    r.add_argument("--hot", action="store_true", help="random start (U(1), Z2; for the confined controls)")
    r.add_argument("--gf-tmax", type=float, default=0.0, help="flow on to this t after the last blocking point (plaquette only, "
                   "for the gradient-flow coupling); 0: stop at the last blocking point")
    s = sub.add_parser("selftest")
    s.add_argument("--gpu", action="store_true")
    bch = sub.add_parser("bench")
    bch.add_argument("--cpu", action="store_true")
    bch.add_argument("--N", type=int, default=36)
    bch.add_argument("--chains", type=int, default=4)
    a = ap.parse_args()
    return {"run": run, "selftest": selftest, "bench": bench}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
