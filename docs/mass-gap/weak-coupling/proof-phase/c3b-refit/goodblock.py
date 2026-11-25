"""The real click test (cycle 3, workstream 2, c3b-refit; PREREG.md in this folder): Leg C's refit of the blocked SU(2) action with the
GOOD BLOCKING of formal/ProofPhase/RouteA/Blocking.lean as the block variable, with a content check.

A periodic N^4 lattice is simulated at bare coupling beta (Leg C's generator: ../../attempts/r3-blocked/blocked.py and
../../../lattice/boundary.py, both imported, never edited; fused CUDA heat bath for SU(2) on the GPU). Direction 0 is time.

The block variable (Blocking.lean, `smearBlock w`, iterated as `smearIter`): one step maps links of length l to links of length 2l.
For the coarse link (y, mu) the transports along the straight path y -> y + 2l mu and, with weight w, along the staples
y -> y +- l nu -> y +- l nu + 2l mu -> y + 2l mu for every SPATIAL nu != mu (both signs; 4 staples for a spatial link, 6 for a temporal
one) are summed and projected: SU(2) A -> A / sqrt(det A) (= q / |q| for a quaternion sum), U(1) the angle of the sum, Z2 the sign
of the sum. Spatial coarse links use only their own fine time slice; temporal coarse links only their time strip (temporal
decimation). w = 0 is plain decimation (Blocking.lean `smearBlock_zero`). Block size b = 2^n after n steps.

Implementation: level 1 is computed at the even fine sites (index takes); every later level on the same even grid (spacing 2), with
links of length 2^k fine = 2^(k-1) grid units, so that every even fine site is a coarse origin. The coarse lattices of block size b
are all (b/2)^4 sublattices {o + (b/2) X} of the even grid (o in {0..b/2-1}^4), stacked into the batch axis. Each is a periodic
(N/b)^4 lattice of coarse links.

Per configuration and block size b the coarse lattices give (the anisotropic refit; the blocking is not hypercubic, so time-space
(ts) and space-space (ss) plaquettes carry separate couplings):
  SU(2) Schwinger-Dyson sums, basis fund_ts, fund_ss, adj_ts, adj_ss (chi_1/3), spin3/2_ts, spin3/2_ss (chi_3/2/4), rect (1x2, pooled);
  U(1)  basis q1_ts, q1_ss, q2_ts, q2_ss, q3_ts, q3_ss, rect;   Z2: joint histogram of (x_ts, x_ss, y_rect) for pseudo-likelihood;
  coarse plaquettes per class (fundamental and adjoint), and the Wilson loops (1,1), (2,2), (2,1), (1,2) of the level-(n-1)
  lattices (half block) per plane class, fundamental and adjoint (the Creutz part of the content check, and the retention ratios).

Usage
  python goodblock.py run GROUP BETA N BLOCKS N_THERM N_MEAS SEED OUT.npz [--chains 2] [--every 4] [--n-or 3] [--w W] [--cpu] [--hot]
  python goodblock.py runplan NAME OUTDIR [--cpu]      one entry of PLAN (the pre-registered GPU plan)
  python goodblock.py plannames
  python goodblock.py selftest [--gpu]
  python goodblock.py bench [--cpu] [--N 48] [--chains 2]
"""

import argparse
import importlib.util
import math
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
LEGC = os.path.normpath(os.path.join(HERE, "..", "..", "attempts", "r3-blocked"))
_spec = importlib.util.spec_from_file_location("blocked", os.path.join(LEGC, "blocked.py"))
BL = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(BL)  # Leg C's module (imports ../../../lattice/boundary.py as BL.BD); read-only use
BD = BL.BD

TIME = 0
W_DEFAULT = 2.0  # pre-registered (PREREG.md, "The weight w"; wscan.py)
BASIS = {"su2": ("fund_ts", "fund_ss", "adj_ts", "adj_ss", "s32_ts", "s32_ss", "rect"),
         "u1": ("q1_ts", "q1_ss", "q2_ts", "q2_ss", "q3_ts", "q3_ss", "rect"), "z2": ("plaq_ts", "plaq_ss", "rect")}
Z2_BINS = (7, 5, 19)  # x_ts = sigma * sum of ts staples in -6..6, x_ss in -4..4, y = rectangles in -18..18 (even steps)
LOOPS = ((1, 1), (2, 2), (2, 1), (1, 2))  # (R along mu, T along nu), mu < nu; Creutz chi = -ln(W22 W11 / (W21 W12))


def transverse(mu):
    """Blocking.lean `transverse`: the spatial directions other than mu."""
    return [nu for nu in range(4) if nu != TIME and nu != mu]


def plane_class(mu, nu):
    return 0 if TIME in (mu, nu) else 1  # 0: time-space (ts), 1: space-space (ss)


def ev(nu, k):
    v = [0, 0, 0, 0]
    v[nu] = k
    return v


def vadd(*vs):
    return [sum(c) for c in zip(*vs)]


# ---------------------------------------------------------------------------------------------------------------------------- blocking

def proj(ops, S):
    """Projection of a path sum: SU(2) q / |q| (= A / sqrt(det A)), U(1) the angle, Z2 the sign (angle 0 or pi)."""
    xp = ops.xp
    if ops.group == "su2":
        n = xp.sqrt((S * S).sum(axis=0, keepdims=True))
        unit = xp.zeros_like(S)
        unit[0] = 1.0
        return xp.where(n > 1e-300, S / xp.maximum(n, 1e-300), unit)  # n = 0 only on a null set (Blocking.lean: then 1)
    if ops.group == "z2":
        return xp.where(S.real < 0, np.pi, 0.0)
    return xp.angle(S)


def to_acc(ops, x):
    return x if ops.group == "su2" else ops.xp.exp(1j * x)


def smear_step(ops, F, lg, w, at):
    """One step of Blocking.lean's smearBlock: F[mu] = links of length lg (input-grid units); at(x, off) = field x at the output points
    shifted by off (input-grid units). Returns the projected sums (straight path + w * spatial staples) on the output points."""
    mul, dag = ops.mul, ops.dag
    o = [0, 0, 0, 0]
    out = []
    for mu in range(4):
        acc = to_acc(ops, mul(at(F[mu], o), at(F[mu], ev(mu, lg))))
        for nu in transverse(mu):
            up = mul(mul(mul(at(F[nu], o), at(F[mu], ev(nu, lg))), at(F[mu], vadd(ev(nu, lg), ev(mu, lg)))),
                     dag(at(F[nu], ev(mu, 2 * lg))))
            dn = mul(mul(mul(dag(at(F[nu], ev(nu, -lg))), at(F[mu], ev(nu, -lg))), at(F[mu], vadd(ev(nu, -lg), ev(mu, lg)))),
                     at(F[nu], vadd(ev(nu, -lg), ev(mu, 2 * lg))))
            acc = acc + w * (to_acc(ops, up) + to_acc(ops, dn))
        out.append(proj(ops, acc))
    return out


def take_at(ops, N, stride):
    """at() for level 1: the fine field at the points stride * z + off (z on the output grid of side N / stride)."""
    xp = ops.xp

    def at(x, off):
        for a in range(4):
            idx = xp.asarray((off[a] + stride * np.arange(N // stride)) % N)
            x = xp.take(x, idx, axis=ops.ax0 + a)
        return x
    return at


def roll_at(ops):
    return lambda x, off: BL.shift(ops, x, off)


def good_levels(ops, U, nmax, w):
    """H[k] (k = 1..nmax): level-k links (length 2^k fine) at every even fine site, on the even grid (side N / 2)."""
    N = U[0].shape[ops.ax0]
    assert N % 2 == 0
    H = [None, smear_step(ops, U, 1, w, take_at(ops, N, 2))]
    for k in range(2, nmax + 1):
        H.append(smear_step(ops, H[k - 1], 2 ** (k - 2), w, roll_at(ops)))
    return H


def lattices(ops, H, s):
    """All sublattices {o + s X} (o in {0..s-1}^4) of a field on a grid whose links have length s grid units: each a periodic lattice
    with unit links; stacked into the batch axis (batch-major, then origins row-major)."""
    xp = ops.xp
    out = []
    for x in H:
        G = x.shape[ops.ax0]
        assert G % s == 0
        Nc = G // s
        lead = x.shape[:ops.ax0]
        k0 = len(lead)
        v = x.reshape(lead + (Nc, s) * 4)
        perm = list(range(k0)) + [k0 + 1, k0 + 3, k0 + 5, k0 + 7] + [k0, k0 + 2, k0 + 4, k0 + 6]
        v = v.transpose(perm).reshape(lead[:-1] + (lead[-1] * s ** 4,) + (Nc,) * 4)
        out.append(xp.ascontiguousarray(v))
    return out


def coarse(ops, H, U, n):
    """Coarse lattices of block size b = 2^n (n >= 1); n = 0 returns the fine field."""
    if n == 0:
        return U
    return lattices(ops, H[n], 2 ** (n - 1))


# ---------------------------------------------------------------------------------------------------------------------------- SD sums

def sd_su2_aniso(ops, V):
    """Anisotropic Schwinger-Dyson sums (basis BASIS['su2']), M (7, 7), c (7), and obs (fund_ts, fund_ss, adj_ts, adj_ss, rect):
    Leg C's sd_su2 with the plaquette sums split by plane class."""
    xp = ops.xp
    K = 7
    Ms, cs, ob = [], [], np.zeros(5)
    cnt = np.zeros(2)
    for mu in range(4):
        u = V[mu]
        steps = BL.PLAQ[mu]
        nus = [nu for nu in range(4) if nu != mu for _ in (0, 1)]
        a = [ops.dag(BL.path(ops, V, mu, st)) for st in steps]
        R = None
        for st in BL.RECT[mu]:
            r = ops.dag(BL.path(ops, V, mu, st))
            R = r if R is None else R + r
        t = [ops.dot(u, ak) for ak in a]
        z = 0 * u
        zs = 0 * t[0]
        g = [None] * K
        cv = [None] * K
        for cl in (0, 1):
            ks = [k for k in range(6) if plane_class(mu, nus[k]) == cl]
            if not ks:
                g[cl], g[2 + cl], g[4 + cl] = z, z, z
                cv[cl], cv[2 + cl], cv[4 + cl] = zs, zs, zs
                continue
            A = sum(a[k] for k in ks)
            uA = sum(t[k] for k in ks)
            B1 = sum(t[k] * a[k] for k in ks)
            s2 = sum(t[k] * t[k] for k in ks)
            w3 = {k: 6 * t[k] * t[k] - 1 for k in ks}
            B3 = sum(w3[k] * a[k] for k in ks)
            s3 = sum(w3[k] * t[k] for k in ks)
            g[cl] = A - uA * u
            g[2 + cl] = (8.0 / 3.0) * (B1 - s2 * u)
            g[4 + cl] = B3 - s3 * u
            cv[cl] = 3 * uA
            cv[2 + cl] = (8.0 / 3.0) * (4 * s2 - len(ks))
            cv[4 + cl] = 15 * sum(2 * t[k] ** 3 - t[k] for k in ks)
            ob[cl] += float(uA.mean())
            ob[2 + cl] += float(((4 * s2 - len(ks)) / 3).mean())
            cnt[cl] += len(ks)
        uR = ops.dot(u, R)
        g[6] = R - uR * u
        cv[6] = 3 * uR
        ob[4] += float(uR.mean()) / 18
        Ms.append(xp.stack([ops.dot(g[i], g[j]).mean() for i in range(K) for j in range(K)]))
        cs.append(xp.stack([x.mean() for x in cv]))
    M = BL.to_host(sum(Ms)).reshape(K, K) / 4
    obs = np.array([ob[0] / cnt[0], ob[1] / cnt[1], ob[2] / cnt[0], ob[3] / cnt[1], ob[4] / 4])
    return M, BL.to_host(sum(cs)) / 4, obs


def sd_u1_aniso(ops, V):
    """U(1) analogue (basis BASIS['u1']); obs (cos_ts, cos_ss, cos2_ts, cos2_ss, rect)."""
    xp = ops.xp
    K = 7
    Ms, cs, ob = [], [], np.zeros(5)
    cnt = np.zeros(2)
    for mu in range(4):
        th = V[mu]
        nus = [nu for nu in range(4) if nu != mu for _ in (0, 1)]
        c = [th + BL.path(ops, V, mu, st) for st in BL.PLAQ[mu]]
        zr = sum(xp.exp(1j * (th + BL.path(ops, V, mu, st))) for st in BL.RECT[mu])
        zs = 0 * th
        g = [None] * K
        cv = [None] * K
        for cl in (0, 1):
            ks = [k for k in range(6) if plane_class(mu, nus[k]) == cl]
            if not ks:
                for j in (cl, 2 + cl, 4 + cl):
                    g[j], cv[j] = zs, zs
                continue
            g[cl] = -sum(xp.sin(c[k]) for k in ks)
            g[2 + cl] = -2 * sum(xp.sin(2 * c[k]) for k in ks)
            g[4 + cl] = -3 * sum(xp.sin(3 * c[k]) for k in ks)
            c1 = sum(xp.cos(c[k]) for k in ks)
            c2 = sum(xp.cos(2 * c[k]) for k in ks)
            cv[cl] = c1
            cv[2 + cl] = 4 * c2
            cv[4 + cl] = 9 * sum(xp.cos(3 * c[k]) for k in ks)
            ob[cl] += float(c1.mean())
            ob[2 + cl] += float(c2.mean())
            cnt[cl] += len(ks)
        g[6] = -zr.imag
        cv[6] = zr.real
        ob[4] += float(zr.real.mean()) / 18
        Ms.append(xp.stack([(g[i] * g[j]).mean() for i in range(K) for j in range(K)]))
        cs.append(xp.stack([x.mean() for x in cv]))
    obs = np.array([ob[0] / cnt[0], ob[1] / cnt[1], ob[2] / cnt[0], ob[3] / cnt[1], ob[4] / 4])
    return BL.to_host(sum(Ms)).reshape(K, K) / 4, BL.to_host(sum(cs)) / 4, obs


def hist_z2_aniso(ops, V):
    """Z2: joint histogram over coarse links of (x_ts, x_ss, y) = sigma * (sum of ts staples, ss staples, rectangle staples), the
    sufficient statistic of the anisotropic pseudo-likelihood; obs (plaq_ts, plaq_ss, 0, 0, rect)."""
    xp = ops.xp
    H = None
    ob, cnt = np.zeros(5), np.zeros(2)
    for mu in range(4):
        th = V[mu]
        nus = [nu for nu in range(4) if nu != mu for _ in (0, 1)]
        p = [xp.cos(th + BL.path(ops, V, mu, st)) for st in BL.PLAQ[mu]]
        xs = []
        for cl in (0, 1):
            ks = [k for k in range(6) if plane_class(mu, nus[k]) == cl]
            x = sum(p[k] for k in ks) if ks else 0 * th
            xs.append(x)
            if ks:
                ob[cl] += float(x.mean())
                cnt[cl] += len(ks)
        y = sum(xp.cos(th + BL.path(ops, V, mu, st)) for st in BL.RECT[mu])
        ob[4] += float(y.mean()) / 18
        i0 = xp.rint((xs[0] + 6) / 2).astype(xp.int64)
        i1 = xp.rint((xs[1] + 4) / 2).astype(xp.int64)
        i2 = xp.rint((y + 18) / 2).astype(xp.int64)
        h = xp.bincount(((i0 * Z2_BINS[1] + i1) * Z2_BINS[2] + i2).ravel(), minlength=int(np.prod(Z2_BINS)))
        H = h if H is None else H + h
    obs = np.array([ob[0] / cnt[0], ob[1] / cnt[1], 0.0, 0.0, ob[4] / 4])
    return BL.to_host(H).reshape(Z2_BINS), obs


def loops(ops, W):
    """Mean Wilson loops of a (coarse) configuration: array (2 plane classes, 4 sizes LOOPS, 2 reps: fundamental (1/2) tr (cos),
    adjoint chi_1 / 3 = (4 t^2 - 1) / 3 (cos 2 theta))."""
    xp = ops.xp
    lines = []
    for mu in range(4):
        d = {1: W[mu]}
        d[2] = ops.mul(W[mu], BL.sh(ops, W[mu], mu, 1))
        lines.append(d)
    out = np.zeros((2, 4, 2))
    n = np.zeros(2)
    for mu in range(4):
        for nu in range(mu + 1, 4):
            cl = plane_class(mu, nu)
            n[cl] += 1
            for j, (R, T) in enumerate(LOOPS):
                a = ops.mul(lines[mu][R], BL.sh(ops, lines[nu][T], mu, R))
                b = ops.mul(lines[nu][T], BL.sh(ops, lines[mu][R], nu, T))
                if ops.group == "su2":
                    t = ops.dot(a, b)
                    f, ad = t, (4 * t * t - 1) / 3
                else:
                    ang = a - b
                    f, ad = xp.cos(ang), xp.cos(2 * ang)
                out[cl, j, 0] += float(f.mean())
                out[cl, j, 1] += float(ad.mean())
    return out / n[:, None, None]


# ---------------------------------------------------------------------------------------------------------------------------- measure

def measure_config(group, ops, U, blocks, w):
    """Per block size b: (M, c, obs, loops) (SU(2), U(1)) or (hist, obs, loops) (Z2); loops are those of the half-block lattices."""
    ns = [int(round(math.log2(b))) for b in blocks]
    assert all(2 ** n == b and n >= 1 for n, b in zip(ns, blocks)), "block sizes must be powers of 2"
    H = good_levels(ops, U, max(ns), w)
    res = []
    for n in ns:
        V = coarse(ops, H, U, n)
        if group == "su2":
            M, c, obs = sd_su2_aniso(ops, V)
        elif group == "u1":
            M, c, obs = sd_u1_aniso(ops, V)
        else:
            Hz, obs = hist_z2_aniso(ops, V)
        del V
        lp = loops(ops, coarse(ops, H, U, n - 1))
        res.append((M, c, obs, lp) if group != "z2" else (Hz, obs, lp))
    return res


def chain_q(group, xp, upd, c):
    """Chain c of the updater in this module's layout, without copying the other chains (GPU SU(2): straight from the 2x2 form)."""
    if group == "su2" and hasattr(upd, "g"):
        return [xp.ascontiguousarray(xp.moveaxis(BD.m2q(u[c:c + 1], xp), -1, 0)) for u in upd.g.U]
    return BL.chain_config(group, xp, upd.links(), c)


def run(a):
    gpu = not a.cpu
    xp = BD.get_xp(gpu)
    blocks = [int(x) for x in str(a.blocks).split(",")]
    for b in blocks:
        if a.N % b or a.N // b < 3:
            raise SystemExit(f"block {b}: must divide N = {a.N} with N / b >= 3")
    box = BL.PeriodicBox(a.N)
    B = a.chains
    upd = BL.make_updater(a.group, box, a.beta, B, a.seed, gpu, a.hot)
    ops = BL.make_ops(a.group, xp)
    t0 = time.time()
    for _ in range(a.n_therm):
        upd.sweep(a.n_or)
    print(f"{a.group} beta={a.beta} N={a.N} w={a.w} thermalised ({a.n_therm} sweeps) t={time.time() - t0:.0f}s; blocks {blocks}", flush=True)
    rec = {"M": [], "c": [], "hist": [], "obs": [], "loops": []}

    def save(m, partial):
        out = dict(group=a.group, beta=a.beta, N=a.N, blocks=np.array(blocks), w=a.w, chains=B, n_therm=a.n_therm, every=a.every,
                   n_or=a.n_or, seed=a.seed, hot=int(a.hot), backend="gpu" if gpu else "cpu", basis=np.array(BASIS[a.group]),
                   seconds=time.time() - t0, partial=int(partial), n_done=m, obs=np.array(rec["obs"]), loops=np.array(rec["loops"]))
        if a.group == "z2":
            out["hist"] = np.array(rec["hist"]).astype(np.int32)
        else:
            out["M"], out["c"] = np.array(rec["M"]), np.array(rec["c"])
        np.savez(a.out, **out)

    for m in range(a.n_meas):
        for _ in range(a.every):
            upd.sweep(a.n_or)
        per = {k: [] for k in rec}
        for c in range(B):
            U = chain_q(a.group, xp, upd, c)
            res = measure_config(a.group, ops, U, blocks, a.w)
            del U
            if a.group == "z2":
                per["hist"].append([r[0] for r in res])
            else:
                per["M"].append([r[0] for r in res])
                per["c"].append([r[1] for r in res])
            per["obs"].append([r[-2] for r in res])
            per["loops"].append([r[-1] for r in res])
        for k, v in per.items():
            if v:
                rec[k].append(v)
        if m % 10 == 9 or m == 0:
            save(m + 1, True)
            o = np.array(rec["obs"][-1]).mean(axis=0)
            print(f"{a.group} beta={a.beta} N={a.N} meas {m + 1}/{a.n_meas} t={time.time() - t0:.0f}s coarse plaq (ts, ss) per b "
                  f"{np.round(o[:, :2], 5).tolist()} adj (ts, ss) {np.round(o[:, 2:4], 5).tolist()}", flush=True)
    save(a.n_meas, False)
    print(f"done {a.out} in {time.time() - t0:.0f}s", flush=True)
    return 0


# ---------------------------------------------------------------------------------------------------------------------------- plan

# The pre-registered GPU plan (PREREG.md "Runs"); queue_refit_gpu.ps1 runs exactly these, in this order.
# (name, group, beta, N, blocks, n_therm, n_meas, chains, every, hot, seed)
PLAN = [
    ("u1_b1.1_N48", "u1", 1.1, 48, "4,8,16", 200, 80, 2, 4, False, 5101),     # photon gate (Coulomb)
    ("z2_b0.6_N48", "z2", 0.6, 48, "4,8,16", 200, 80, 2, 4, False, 5102),     # deconfined Z2 gate
    ("su2_b2.3_N48", "su2", 2.3, 48, "4,8,16", 300, 250, 2, 4, False, 5103),  # L sqrt(sigma) = 1.40, 2.80, 5.60
    ("su2_b2.4_N48", "su2", 2.4, 48, "4,8,16", 300, 150, 2, 4, False, 5105),  # 1.03, 2.06, 4.13
    ("su2_b2.5_N48", "su2", 2.5, 48, "4,8,16", 300, 250, 2, 4, False, 5104),  # 0.73, 1.46, 2.92 (scaling partner of 2.80)
]


def plan_args(entry, outdir, cpu=False):
    name, g, beta, N, blocks, th, nm, ch, ev_, hot, seed = entry
    ns = argparse.Namespace(group=g, beta=beta, N=N, blocks=blocks, n_therm=th, n_meas=nm, seed=seed,
                            out=os.path.join(outdir, name + ".npz"), chains=ch, every=ev_, n_or=3, w=W_DEFAULT, cpu=cpu, hot=hot)
    return ns


# ---------------------------------------------------------------------------------------------------------------------------- tests

def naive_link(U, level, x, mu, w, N):
    """Independent reference: the level-`level` good-blocking link from fine site x in direction mu, by explicit recursion over paths
    with scalar quaternion arithmetic (numpy, last-axis layout of one configuration: U[mu][x0, x1, x2, x3] -> (4,))."""
    q = BD.qmul

    def dg(a):
        return a * np.array([1.0, -1.0, -1.0, -1.0])

    def link(k, y, m):
        y = tuple(int(v) % N for v in y)
        if k == 0:
            return U[m][y]
        L = 2 ** (k - 1)

        def lk(z, d, fwd=True):
            if fwd:
                return link(k - 1, z, d)
            zz = list(z)
            zz[d] -= L
            return dg(link(k - 1, zz, d))

        def mv(z, d, s):
            zz = list(z)
            zz[d] += s * L
            return zz
        S = q(lk(y, m), lk(mv(y, m, 1), m))
        for nu in transverse(m):
            for s in (1, -1):
                p = lk(y, nu, s > 0)
                z = mv(y, nu, s)
                p = q(p, lk(z, m))
                z = mv(z, m, 1)
                p = q(p, lk(z, m))
                z = mv(z, m, 1)
                p = q(p, lk(z, nu, s < 0))
                S = S + w * p
        return S / np.linalg.norm(S)
    return link(level, x, mu)


def metropolis_aniso(group, cpl, U, n_sweeps, rng, hits=4, eps=0.6):
    """Metropolis for an anisotropic plaquette action (test only): SU(2) sum_p [bF(p) (1/2) tr + bA(p) chi_1 / 3], U(1)
    sum_p [q1(p) cos + q2(p) cos 2], couplings per plane class cpl = (F_ts, F_ss, A_ts, A_ss). Checkerboard (direction, parity)."""
    ops = BL.make_ops(group, np)
    box = BL.PeriodicBox(U[0].shape[-1])
    B = U[0].shape[ops.ax0 - 1]
    acc, tot = 0, 0
    for _ in range(n_sweeps):
        for mu in range(4):
            nus = [nu for nu in range(4) if nu != mu for _ in (0, 1)]
            cls = [plane_class(mu, nu) for nu in nus]
            for p in (0, 1):
                m = box.parity[p][None]
                a = [BL.path(ops, U, mu, st) for st in BL.PLAQ[mu]]
                if group == "su2":
                    a = [ops.dag(x) for x in a]

                def local(u):
                    if group == "su2":
                        return sum(cpl[c] * ops.dot(u, ak) + cpl[2 + c] * (4 * ops.dot(u, ak) ** 2 - 1) / 3 for ak, c in zip(a, cls))
                    return sum(cpl[c] * np.cos(u + ak) + cpl[2 + c] * np.cos(2 * (u + ak)) for ak, c in zip(a, cls))
                for _ in range(hits):
                    u = U[mu]
                    if group == "su2":
                        new = BL.renorm(np, ops.mul(BL.qexp(np, eps * rng.normal(size=(3,) + u.shape[1:])), u))
                    else:
                        new = u + 1.5 * eps * rng.normal(size=u.shape)
                    dS = local(new) - local(u)
                    okm = (np.log(rng.random(size=dS.shape)) < dS) & m
                    U[mu] = np.where(okm[None], new, u) if group == "su2" else np.where(okm, new, u)
                    acc += int(okm.sum())
                    tot += int(m.sum()) * B
    return U, acc / max(tot, 1)


def selftest(a):
    ok = True

    def report(name, good, detail):
        nonlocal ok
        ok &= bool(good)
        print(f"{'PASS' if good else 'FAIL'}  {name}: {detail}", flush=True)

    rng = np.random.default_rng(31)
    qo, ao, zo = BL.QOps(np), BL.AOps(np, "u1"), BL.AOps(np, "z2")

    def rand_su2(N, B=1):
        return [BL.renorm(np, rng.normal(size=(4, B) + (N,) * 4)) for _ in range(4)]

    w = W_DEFAULT
    # 1. independent path recursion: level-1, -2 and -3 links at random even sites, spatial and temporal, against the array code
    N = 8
    U = rand_su2(N)
    H = good_levels(qo, U, 3, w)
    Ul = [np.moveaxis(u[:, 0], 0, -1) for u in U]  # (N,N,N,N,4)
    err = 0.0
    for trial in range(12):
        k = 1 + trial % 3
        mu = trial % 4
        x = 2 * rng.integers(0, N // 2, size=4)
        ref = naive_link(Ul, k, x, mu, w, N)
        got = H[k][mu][(slice(None), 0) + tuple(x // 2)]
        err = max(err, float(np.abs(ref - got).max()))
    report("good blocking = independent path recursion (levels 1-3, w = 2, spatial and temporal links)", err < 1e-12, f"max {err:.1e}")

    # 2. w = 0 is decimation: the coarse lattices at origins {0, b/2}^4 equal Leg C's path product (blocked.block, f = 0)
    for b in (2, 4, 8):
        n = int(math.log2(b))
        H0 = good_levels(qo, U, n, 0.0)
        V = coarse(qo, H0, U, n)
        Vc = BL.block(qo, U, b)  # origins {0, b//2}^4
        s = max(b // 2, 1)
        if b > 2:
            # origins in grid units of the even grid: fine b/2 -> grid b/4; our origin index runs over {0..b/2-1}^4 grid units
            g = b // 4
            sel = [((o0 * s + o1) * s + o2) * s + o3 for o0 in (0, g) for o1 in (0, g) for o2 in (0, g) for o3 in (0, g)]
            d = max(float(np.abs(V[mu][:, sel] - Vc[mu]).max()) for mu in range(4))
        else:
            d = max(float(np.abs(V[mu][:, :1] - Vc[mu][:, :1]).max()) for mu in range(4))  # b = 2: only origin 0 is on the even grid
        report(f"w = 0 is decimation (Blocking.lean smearBlock_zero): b = {b} equals Leg C's path product", d < 1e-12, f"{d:.1e}")

    # 3. gauge covariance: SD sums, coarse plaquettes and loops invariant under a random fine gauge transformation
    N = 8
    U = rand_su2(N)
    g = BL.renorm(np, rng.normal(size=(4, 1) + (N,) * 4))
    Ug = [qo.mul(qo.mul(g, U[mu]), qo.dag(BL.sh(qo, g, mu))) for mu in range(4)]
    r1 = measure_config("su2", qo, U, [2, 4], w)
    r2 = measure_config("su2", qo, Ug, [2, 4], w)
    d = max(max(float(np.abs(np.asarray(x) - np.asarray(y)).max()) for x, y in zip(p1, p2)) for p1, p2 in zip(r1, r2))
    report("SU(2) gauge covariance of the good blocking (b = 2, 4): SD sums, plaquettes, loops invariant", d < 1e-10, f"{d:.1e}")
    th = [rng.uniform(-np.pi, np.pi, size=(1,) + (N,) * 4) for _ in range(4)]
    gu = rng.uniform(-np.pi, np.pi, size=(1,) + (N,) * 4)
    thg = [th[mu] + gu - BL.sh(ao, gu, mu) for mu in range(4)]
    r1 = measure_config("u1", ao, th, [2, 4], w)
    r2 = measure_config("u1", ao, thg, [2, 4], w)
    d = max(max(float(np.abs(np.asarray(x) - np.asarray(y)).max()) for x, y in zip(p1, p2)) for p1, p2 in zip(r1, r2))
    report("U(1) gauge covariance of the good blocking: invariant", d < 1e-10, f"{d:.1e}")

    # 4. time reflection (Blocking.lean smearBlock_thetaConn): blocking commutes with Theta (t -> -t) at origin 0
    def theta_su2(U):
        """(Theta U)(x, i) = U(Theta x, i); (Theta U)(x, 0) = U(Theta x - e0, 0)^dagger; Theta x = (-x0, x1, x2, x3)."""
        R = [np.roll(np.flip(u, axis=2), 1, axis=2) for u in U]
        R[0] = qo.dag(BL.sh(qo, R[0], 0, 1))
        return R
    U = rand_su2(8)
    # check Theta is the reflection x0 -> -x0: temporal link (x, 0) -> inverse of the temporal link at (-x0 - 1)
    TU = theta_su2(U)
    chk = abs(TU[0][(slice(None), 0, 3, 1, 2, 5)] - qo.dag(U[0][(slice(None), 0, (-3 - 1) % 8, 1, 2, 5)])).max() + \
        abs(TU[2][(slice(None), 0, 3, 1, 2, 5)] - U[2][(slice(None), 0, (-3) % 8, 1, 2, 5)]).max()
    Ha = good_levels(qo, TU, 2, w)
    Hb = good_levels(qo, U, 2, w)
    Va = coarse(qo, Ha, TU, 2)
    Vb = coarse(qo, Hb, U, 2)
    Vb0 = [v[:, :1] for v in Vb]
    Va0 = [v[:, :1] for v in Va]
    TVb = theta_su2(Vb0)
    d = max(float(np.abs(Va0[mu] - TVb[mu]).max()) for mu in range(4))
    report("time reflection commutes with the good blocking (b = 4, origin 0; Blocking.lean smearBlock_thetaConn)", d < 1e-12 and chk < 1e-15,
           f"{d:.1e} (reflection check {chk:.1e})")

    # 5. subgroups: SU(2) blocking of a U(1)-subgroup field = U(1) blocking; of a centre-valued field = Z2 blocking (w = 2: no ties)
    al = [rng.uniform(-np.pi, np.pi, size=(1,) + (8,) * 4) for _ in range(4)]
    Ue = [np.stack([np.cos(x), 0 * x, 0 * x, np.sin(x)]) for x in al]
    He, Ha_ = good_levels(qo, Ue, 3, w), good_levels(ao, al, 3, w)
    d = max(float(np.abs(np.angle(np.exp(1j * (np.arctan2(He[k][mu][3], He[k][mu][0]) - Ha_[k][mu])))).max()) for k in (1, 2, 3) for mu in range(4))
    report("SU(2) blocking of a U(1)-subgroup field = U(1) blocking (levels 1-3)", d < 1e-12, f"{d:.1e}")
    zz = [np.pi * rng.integers(0, 2, size=(1,) + (8,) * 4).astype(float) for _ in range(4)]
    Uz = [np.stack([np.cos(x), 0 * x, 0 * x, 0 * x]) for x in zz]
    Hq, Hz = good_levels(qo, Uz, 3, w), good_levels(zo, zz, 3, w)
    d = max(float(np.abs(Hq[k][mu][0] - np.cos(Hz[k][mu])).max()) for k in (1, 2, 3) for mu in range(4))
    vals = np.unique(np.concatenate([np.round(Hz[k][mu].ravel(), 12) for k in (1, 2, 3) for mu in range(4)]))
    report("SU(2) blocking of a centre-valued field = Z2 blocking; Z2 values stay in {0, pi}", d < 1e-12 and set(vals) <= {0.0, round(np.pi, 12)},
           f"{d:.1e}; values {vals}")

    # 6. anisotropic SD sums: plane split adds up to Leg C's isotropic sums; Wilson configurations at b = 1 give (beta, beta, 0, 0)
    U = rand_su2(4)
    M7, c7, o7 = sd_su2_aniso(qo, U)
    M4, c4, o4 = BL.sd_su2(qo, U)
    T = np.zeros((4, 7))
    T[0, 0] = T[0, 1] = T[1, 2] = T[1, 3] = T[2, 4] = T[2, 5] = T[3, 6] = 1
    d = max(np.abs(T @ M7 @ T.T - M4).max(), np.abs(T @ c7 - c4).max(), abs((o7[0] + o7[1]) / 2 - o4[0]), abs((o7[2] + o7[3]) / 2 - o4[1]),
            abs(o7[4] - o4[2]))
    report("anisotropic SD sums add up to Leg C's isotropic sums (M, c, plaquettes)", d < 1e-12, f"{d:.1e}")
    box = BL.PeriodicBox(6)
    for grp, beta in (("su2", 2.3), ("u1", 1.1)):
        upd = BL.make_updater(grp, box, beta, 4, 7, False)
        for _ in range(100):
            upd.sweep(3)
        Ms, cs = [], []
        ops = BL.make_ops(grp, np)
        for _ in range(30):
            for _ in range(4):
                upd.sweep(3)
            L = upd.links()
            for c in range(4):
                V = BL.chain_config(grp, np, L, c)
                M, cc, _ = sd_su2_aniso(ops, V) if grp == "su2" else sd_u1_aniso(ops, V)
                Ms.append(M)
                cs.append(cc)
        bb, ee = BL.jk_fit(np.array(Ms), np.array(cs), [0, 1, 2, 3])
        good = all(abs(bb[i] - beta) < max(4 * ee[i], 0.03 * beta) for i in (0, 1)) and all(abs(bb[i]) < max(4 * ee[i], 0.03) for i in (2, 3))
        report(f"{grp} anisotropic SD fit, Wilson beta = {beta} at b = 1 (6^4, 120 configs)", good, f"{np.round(bb, 4)} +- {np.round(ee, 4)}")

    # 7. known anisotropic mixed actions (independent Metropolis) recovered by the anisotropic SD fit
    for grp, cpl in (("su2", (1.2, 0.7, 0.6, 0.2)), ("u1", (0.8, 0.4, 0.3, 0.1))):
        ops = BL.make_ops(grp, np)
        rngm = np.random.default_rng(41)
        Uc = BL.cold(grp, BL.PeriodicBox(4), 4)
        if grp == "su2":
            Uc = [np.ascontiguousarray(np.moveaxis(u, -1, 0)) for u in Uc]
        Uc, acc = metropolis_aniso(grp, cpl, Uc, 150, rngm)
        Ms, cs = [], []
        for _ in range(60):
            Uc, acc = metropolis_aniso(grp, cpl, Uc, 3, rngm)
            for c in range(4):
                V = [u[:, c:c + 1] if grp == "su2" else u[c:c + 1] for u in Uc]
                M, cc, _ = sd_su2_aniso(ops, V) if grp == "su2" else sd_u1_aniso(ops, V)
                Ms.append(M)
                cs.append(cc)
        bb, ee = BL.jk_fit(np.array(Ms), np.array(cs), [0, 1, 2, 3])
        good = all(abs(bb[i] - cpl[i]) < max(4 * ee[i], 0.05) for i in range(4))
        report(f"{grp} anisotropic SD fit recovers a known anisotropic action {cpl} (Metropolis 4^4, 240 configs, acc {acc:.2f})", good,
               f"{np.round(bb, 4)} +- {np.round(ee, 4)}")

    # 8. Z2 anisotropic pseudo-likelihood at b = 1 (Wilson beta = 0.3, 0.6) gives (beta, beta)
    sys.path.insert(0, HERE)
    from analyse_refit import z2_fit_aniso, selftest_tables
    dt, det = selftest_tables()
    report("anisotropic pair tables and halves: regression against Leg C (pairs) and workstream A (evaluate_adjoint)", dt < 1e-9, det)
    for beta in (0.3, 0.6):
        upd = BL.make_updater("z2", box, beta, 4, 9, False)
        for _ in range(100):
            upd.sweep(3)
        Hh = 0
        for _ in range(30):
            upd.sweep(3)
            L = upd.links()
            for c in range(4):
                Hh = Hh + hist_z2_aniso(zo, BL.chain_config("z2", np, L, c))[0]
        bz = z2_fit_aniso(Hh, [0, 1])
        bz3 = z2_fit_aniso(Hh, [0, 1, 2])
        report(f"z2 anisotropic pseudo-likelihood, Wilson beta = {beta}, b = 1", all(abs(x - beta) < 0.03 for x in bz),
               f"(ts, ss) {np.round(bz, 4)}; with rect {np.round(bz3, 4)}")

    # 9. loops: W(1,1) of the half-block lattice = coarse plaquette of level n-1; W(2,2) of the fine field at b = 2 equals Leg C's Creutz loop
    U = rand_su2(8)
    lp = loops(qo, U)
    cz = BL.creutz_loops(qo, U, 2)  # (1,1), (2,2), (2,1), (1,2) pooled over the six planes
    d = float(np.abs(lp[:, :, 0].mean(axis=0) - cz).max())
    report("loops (fundamental, pooled over classes) = Leg C's creutz_loops at R0 = 2", d < 1e-12, f"{d:.1e}")

    if a.gpu:
        import cupy as cp
        qg = BL.QOps(cp)
        U = rand_su2(8)
        rc = measure_config("su2", qo, U, [2, 4], w)
        rg = measure_config("su2", qg, [cp.asarray(u) for u in U], [2, 4], w)
        d = max(max(float(np.abs(np.asarray(x) - np.asarray(BD.to_host(y) if hasattr(y, 'get') else y)).max()) for x, y in zip(p1, p2))
                for p1, p2 in zip(rc, rg))
        report(f"GPU = CPU: SU(2) good blocking, SD sums, loops ({'fused kernel' if qg.kernel is not None else 'array code'})", d < 1e-9, f"{d:.1e}")
        th = [rng.uniform(-np.pi, np.pi, size=(1,) + (8,) * 4) for _ in range(4)]
        for grp in ("u1", "z2"):
            x = th if grp == "u1" else [np.pi * (t > 0) for t in th]
            rc = measure_config(grp, BL.AOps(np, grp), x, [2, 4], w)
            rg = measure_config(grp, BL.AOps(cp, grp), [cp.asarray(u) for u in x], [2, 4], w)
            d = max(max(float(np.abs(np.asarray(p) - np.asarray(q)).max()) for p, q in zip(p1, p2)) for p1, p2 in zip(rc, rg))
            report(f"GPU = CPU: {grp} good blocking and sums", d < 1e-9, f"{d:.1e}")
        upd = BL.make_updater("su2", BL.PeriodicBox(8), 2.3, 2, 3, True)
        for _ in range(100):
            upd.sweep(3)
        U0 = chain_q("su2", cp, upd, 1)
        U1 = BL.chain_config("su2", cp, upd.links(), 1)
        d = max(float(cp.abs(x - y).max()) for x, y in zip(U0, U1))
        report("GPU chain extraction straight from the 2x2 form = Leg C's chain_config", d < 1e-15, f"{d:.1e}")
    print("SELFTEST", "OK" if ok else "FAILED")
    return 0 if ok else 1


# ---------------------------------------------------------------------------------------------------------------------------- bench

def bench(a):
    gpu = not a.cpu
    xp = BD.get_xp(gpu)
    sync = (lambda: xp.cuda.Device().synchronize()) if gpu else (lambda: None)
    N, B = a.N, a.chains
    box = BL.PeriodicBox(N)
    blocks = [b for b in (4, 8, 16) if N % b == 0 and N // b >= 3]
    out = {}
    for grp, beta in (("su2", 2.3), ("u1", 1.1), ("z2", 0.6)):
        upd = BL.make_updater(grp, box, beta, B, 1, gpu)
        ops = BL.make_ops(grp, xp)
        upd.sweep(3)
        sync()
        t = time.time()
        for _ in range(2):
            upd.sweep(3)
        sync()
        ts = (time.time() - t) / 2 / B
        U = chain_q(grp, xp, upd, 0)
        measure_config(grp, ops, U, blocks, W_DEFAULT)
        sync()
        t = time.time()
        for _ in range(2):
            U = chain_q(grp, xp, upd, 0)
            measure_config(grp, ops, U, blocks, W_DEFAULT)
        sync()
        tm = (time.time() - t) / 2
        out[grp] = (ts, tm)
        mem = f"; GPU pool {xp.get_default_memory_pool().total_bytes() / 2**30:.2f} GiB" if gpu else ""
        print(f"{grp} N={N} chains={B}: sweep per chain {ts:.3f} s; blocking + measurement per config (blocks {blocks}) {tm:.3f} s{mem}", flush=True)
        del upd, U
        if gpu:
            xp.get_default_memory_pool().free_all_blocks()
    total = 0.0
    for (name, grp, beta, Np, bl, th, nm, ch, every, hot, seed) in PLAN:
        ts, tm = out[grp]
        sc = (Np / N) ** 4
        sec = th * ch * ts * sc + nm * ch * (every * ts * sc + tm * sc)
        total += sec
        print(f"  plan {name}: about {sec / 60:.0f} min")
    print(f"PROJECTED TOTAL for the plan: {total / 3600:.2f} h (excluding selftest and bench, about 5 min)")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("group", choices=("su2", "u1", "z2"))
    r.add_argument("beta", type=float)
    r.add_argument("N", type=int)
    r.add_argument("blocks")
    r.add_argument("n_therm", type=int)
    r.add_argument("n_meas", type=int)
    r.add_argument("seed", type=int)
    r.add_argument("out")
    r.add_argument("--chains", type=int, default=2)
    r.add_argument("--every", type=int, default=4)
    r.add_argument("--n-or", type=int, default=3)
    r.add_argument("--w", type=float, default=W_DEFAULT)
    r.add_argument("--cpu", action="store_true")
    r.add_argument("--hot", action="store_true")
    rp = sub.add_parser("runplan")
    rp.add_argument("name")
    rp.add_argument("outdir")
    rp.add_argument("--cpu", action="store_true")
    sub.add_parser("plannames")
    s = sub.add_parser("selftest")
    s.add_argument("--gpu", action="store_true")
    bch = sub.add_parser("bench")
    bch.add_argument("--cpu", action="store_true")
    bch.add_argument("--N", type=int, default=48)
    bch.add_argument("--chains", type=int, default=2)
    a = ap.parse_args()
    if a.cmd == "plannames":
        print("\n".join(p[0] for p in PLAN))
        return 0
    if a.cmd == "runplan":
        e = [p for p in PLAN if p[0] == a.name]
        if not e:
            raise SystemExit(f"unknown plan entry {a.name}")
        return run(plan_args(e[0], a.outdir, a.cpu))
    return {"run": run, "selftest": selftest, "bench": bench}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
