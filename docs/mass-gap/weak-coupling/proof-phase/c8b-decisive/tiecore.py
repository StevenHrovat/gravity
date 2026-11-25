"""Tie test (c8b-decisive): two degenerate vortex-sheet arrangements, a one-cell breaker, a sampler that sees both (see decisive.py)."""

import glob
import itertools
import math
import os
import sys
import time

sys.dont_write_bytecode = True
import numpy as np

import decisive as D
bd = D.bd


def i2_elements():
    """The 120 elements of the binary icosahedral group as unit quaternions (a0, a1, a2, a3)."""
    phi = (1 + 5 ** 0.5) / 2
    els = set()

    def add(v):
        els.add(tuple(round(x, 12) + 0.0 for x in v))

    for i in range(4):
        for sgn in (1, -1):
            v = [0.0] * 4
            v[i] = float(sgn)
            add(v)
    for sg in itertools.product((0.5, -0.5), repeat=4):
        add(sg)
    base = (phi / 2, 0.5, 1 / (2 * phi), 0.0)
    even = [p for p in itertools.permutations(range(4)) if sum(1 for i in range(4) for j in range(i + 1, 4) if p[i] > p[j]) % 2 == 0]
    for p in even:
        for sg in itertools.product((1, -1), repeat=3):
            vals = [0.0] * 4
            sgs = list(sg) + [1]
            for k in range(4):
                vals[p[k]] = base[k] * sgs[k]
            add(vals)
    return np.array(sorted(els))


class I2Updater:
    """Heat bath for the binary icosahedral gauge group 2I (120 elements, a subgroup of SU(2)): each link is drawn exactly from the
    120-point law p(U) ~ exp(beta Re(U A)), A the staple sum.  Same interface as boundary.U1Updater (no overrelaxation: a sweep is
    1 + n_or heat-bath passes).  Only dynamic links are written."""

    def __init__(self, xp, box, beta, U, seed):
        self.xp, self.box, self.beta = xp, box, beta
        self.ops = bd.SU2Ops(xp)
        self.U = [xp.array(u, dtype=float) for u in U]
        self.rng = D.RNG(xp, seed)
        self.G = xp.asarray(i2_elements())
        self.masks = [[xp.asarray(box.dyn[mu] & box.parity[p]) for p in (0, 1)] for mu in range(4)]

    def set_dynamic(self, dyn):
        self.masks = [[self.xp.asarray(dyn[mu] & self.box.parity[p]) for p in (0, 1)] for mu in range(4)]

    def heatbath(self):
        xp = self.xp
        for mu in range(4):
            for p in (0, 1):
                m = self.masks[mu][p]
                A = bd.staple_generic(self.ops, self.U, mu)[:, m]          # (B, n, 4)
                Ad = A * xp.asarray([1.0, -1.0, -1.0, -1.0])
                sc = self.beta * (Ad @ self.G.T)                           # (B, n, 120): beta Re(U A) for every group element
                sc = sc - sc.max(axis=-1, keepdims=True)
                cs = xp.cumsum(xp.exp(sc), axis=-1)
                u = self.rng.uniform(A.shape[:2]) * cs[..., -1]
                idx = xp.minimum((cs < u[..., None]).sum(axis=-1), 119)
                self.U[mu][:, m] = self.G[idx]

    def sweep(self, n_or):
        for _ in range(1 + n_or):
            self.heatbath()

    def links(self):
        return self.U


def make_tie_updater(group, box, beta, U, seed, gpu):
    if group == "i2":
        return I2Updater(bd.get_xp(gpu), box, beta, U, seed)
    return bd.make_updater(group, box, beta, U, seed, gpu)


def tie_geometry(box, sep=None):
    ell = box.ell
    c = (ell - 1) // 2
    s = sep if sep else max(1, min(int(round((ell - 1) / 4)), c - 1))
    return c, s, ell // 2          # xy centre, sheet offset, t position of the breaker


def tie_state(group, box, B, sep, sector):
    """Initial links.  Sector 'A' = two flat sheets: the boundary data of twist twice (Dirac strings continued through the interior); the
    xy plaquettes at x = c -/+ s, y = c are frustrated for every (z, t).  Sector 'B' = the same with the dynamic y-links at y = c,
    x in c - s + 1 .. c + s, z, t in 1 .. ell - 1 multiplied by the centre element: the sheets are joined into a tube along the four
    walls z, t = 0, ell (frustrated yz and yt plaquettes there, none at the sheet positions in the deep slices)."""
    ell = box.ell
    c, s, t0 = tie_geometry(box, sep)
    f = np.zeros((ell, ell))
    f[c - s, c] = np.pi
    f[c + s, c] = np.pi
    G = np.zeros((ell, ell + 1))
    G[:, :ell] = np.cumsum(f[:, ::-1], axis=1)[:, ::-1]
    A = np.zeros((4,) + box.dims)
    A[0, :ell, :ell + 1] = G[:, :, None, None]
    shape = (B,) + box.dims
    out = []
    for mu in range(4):
        a = np.broadcast_to(A[mu], shape)
        if group in ("su2", "i2"):
            q = np.zeros(shape + (4,))
            q[..., 0] = np.cos(a)
            q[..., 3] = np.sin(a)
            q = np.round(q)
        else:
            q = np.angle(np.exp(1j * np.array(a, dtype=float)))
            q = np.where(np.abs(q) > 1.0, np.pi, 0.0)
        out.append(np.array(q))
    if sector == "B":
        sl = (slice(None), slice(c - s + 1, c + s + 1), c, slice(1, ell), slice(1, ell))
        if group in ("su2", "i2"):
            out[1][sl] = -out[1][sl]
        else:
            out[1][sl] = np.where(out[1][sl] == 0.0, np.pi, 0.0)
    return out


def set_breaker(group, U, box, sep, lam):
    """The one-cell breaker: the frozen y-link on the face z = 0 at (x, y, t) = (c, c, t0) is replaced by the centre element rotated the
    fraction lam of the way (lam = 0 unchanged, lam = 1 the centre element: the yz plaquette at that place changes sign).  This frozen
    link's only dynamic plaquette is the yz plaquette that the tube (sector B) passes and the flat sheets (sector A) do not."""
    c, s, t0 = tie_geometry(box, sep)
    if group in ("su2", "i2"):
        U[1][:, c, c, 0, t0, :] = [np.cos(lam * np.pi), 0.0, 0.0, np.sin(lam * np.pi)]
    else:
        U[1][:, c, c, 0, t0] = lam * np.pi
    return U


def wloop(ops, U, n):
    """Real part of the n x n Wilson loops in the xy plane at every site (base at the lower corner)."""
    Lm, Ln = U[0], U[1]
    for r in range(1, n):
        Lm = ops.mul(Lm, bd.sh(U[0], 0, r))
        Ln = ops.mul(Ln, bd.sh(U[1], 1, r))
    W = ops.mul(ops.mul(Lm, bd.sh(Ln, 0, n)), ops.mul(ops.dag(bd.sh(Lm, 1, n)), ops.dag(Ln)))
    return ops.re(W)


LOOP_R = {"z2": 2, "su2": 2, "i2": 5}


def tie_obs(group, ops, U, box, beta, sep, lam, R=None):
    """Per chain: the sheet indicator f = (1 - W) / 2, W the R x R Wilson loop in the xy plane around each of the two sheet positions
    (loop centred on the sheet plaquette), mean over both positions and the deep (z, t) slices.  A loop that encloses a centre-vortex
    sheet is negative (f above 1/2), one that does not is positive (f below 1/2): sector A (flat sheets) f above 1/2, sector B (tube)
    below.  R = 2 (a thin sheet, Z2, SU(2)); R = 5 for 2I, whose sheet is at least five lattice units thick.  And dS/dlam of the action
    term of the one dynamic plaquette that contains the breaker link."""
    ell = box.ell
    c, s, t0 = tie_geometry(box, sep)
    R = R or LOOP_R[group]
    W = wloop(ops, U, R)
    lo, hi = 2, max(3, ell - 1)
    vals = []
    for d in (-s, s):
        x0, y0 = c + d - (R - 1) // 2, c - (R - 1) // 2
        vals.append(bd.to_host(W[:, x0, y0, lo:hi, lo:hi]).mean(axis=(1, 2)))
    f = (1.0 - np.mean(vals, axis=0)) / 2
    Rr = ops.mul(ops.mul(bd.sh(U[2], 1), ops.dag(bd.sh(U[1], 2))), ops.dag(U[2]))
    phi = lam * np.pi
    if group in ("su2", "i2"):
        r = bd.to_host(Rr[:, c, c, 0, t0, :])
        dS = beta * np.pi * (np.sin(phi) * r[:, 0] + np.cos(phi) * r[:, 3])
    else:
        th = bd.to_host(Rr[:, c, c, 0, t0])
        dS = beta * np.pi * np.sin(phi + th)
    return f, dS


def tie_run(a):
    gpu = not a.cpu
    box = bd.Box(a.ell)
    B = a.chains
    ops = bd.make_ops("su2" if a.group == "i2" else a.group, np)
    t0 = time.time()
    c, s, tb = tie_geometry(box, a.sep)
    U = tie_state(a.group, box, B, a.sep, a.sector)
    U = set_breaker(a.group, U, box, a.sep, 0.0)
    upd = make_tie_updater(a.group, box, a.beta, U, a.seed, gpu)
    for _ in range(a.therm):
        upd.sweep(a.n_or)
    lams = np.linspace(0.0, 1.0, a.nodes)
    F, DS = [], []
    for k, lam in enumerate(lams):
        U = [bd.to_host(u).copy() for u in upd.links()]
        U = set_breaker(a.group, U, box, a.sep, lam)
        upd = make_tie_updater(a.group, box, a.beta, U, a.seed + 100 * (k + 1), gpu)
        for _ in range(a.step_therm):
            upd.sweep(a.n_or)
        fk, dk = [], []
        for m in range(a.meas):
            for _ in range(a.every):
                upd.sweep(a.n_or)
            f, d = tie_obs(a.group, ops, upd.links(), box, a.beta, a.sep, lam)
            fk.append(f)
            dk.append(d)
        F.append(fk)
        DS.append(dk)
        print(f"  lam {lam:.3f}: f {np.mean(fk):.3f} dS/dlam {np.mean(dk):+.3f}  ({time.time() - t0:.0f}s)", flush=True)
    np.savez(a.out, group=a.group, beta=a.beta, ell=a.ell, sep=s, sector=a.sector, chains=B, therm=a.therm, step_therm=a.step_therm,
             meas=a.meas, every=a.every, n_or=a.n_or, nodes=a.nodes, lam=lams, f=np.array(F), dS=np.array(DS), seed=a.seed,
             seconds=time.time() - t0, backend="gpu" if gpu else "cpu")
    print(f"done {a.out} in {time.time() - t0:.0f}s", flush=True)
    return 0


def simpson_w(n):
    h = 1.0 / (n - 1)
    w = np.ones(n)
    w[1:-1:2] = 4
    w[2:-1:2] = 2
    return w * h / 3


def analyse_tie(zA, zB):
    """Ratio method: F_X(1) - F_X(0) = integral of <dS/dlam> in sector X (Simpson on the ladder); delta = (A) - (B) is the shift of
    ln(Z_B / Z_A), the log-odds of the two arrangements, that the breaker causes.  Errors from the independent chains."""
    out = {"group": str(zA["group"]), "beta": float(zA["beta"]), "ell": int(zA["ell"]), "sep": int(zA["sep"]),
           "chains": int(zA["chains"]), "nodes": int(zA["nodes"])}
    n = int(zA["nodes"])
    w = simpson_w(n) if n % 2 == 1 else np.full(n, 1.0 / n)
    res = {}
    for lab, z in (("A", zA), ("B", zB)):
        ch = z["dS"].mean(axis=1)                       # (nodes, chains)
        m = ch.mean(axis=1)
        e = ch.std(axis=1, ddof=1) / math.sqrt(ch.shape[1])
        f = z["f"]                                      # (nodes, meas, chains)
        fch = f.mean(axis=1)
        sw = int(((f[:, 1:, :] - 0.5) * (f[:, :-1, :] - 0.5) < 0).sum())
        res[lab] = {"I": float((w * m).sum()), "I_err": float(math.sqrt(((w * e) ** 2).sum())), "dS": m.tolist(), "dS_err": e.tolist(),
                    "f": fch.mean(axis=1).tolist(), "switches": sw, "f_chain_range": [float(fch.min()), float(fch.max())]}
    out["A"], out["B"] = res["A"], res["B"]
    out["delta"] = res["A"]["I"] - res["B"]["I"]
    out["delta_err"] = math.sqrt(res["A"]["I_err"] ** 2 + res["B"]["I_err"] ** 2)
    out["tie_strength"] = math.tanh(abs(out["delta"]) / 4)
    fa, fb = np.array(res["A"]["f"]), np.array(res["B"]["f"])
    out["f_gap_min"] = float(np.min(np.abs(fa - fb)))
    out["separated"] = bool(out["f_gap_min"] > 0.15 and res["A"]["f_chain_range"][0] > 0.5 and res["B"]["f_chain_range"][1] < 0.5)
    out["mixed"] = bool(np.max(np.abs(fa - fb)) < 0.1)
    avg = 0.5 * (fa + fb)
    out["df_direct"] = float(avg[-1] - avg[0])
    out["verdict"] = tie_verdict(out)
    return out


def tie_verdict(r):
    """Fixed in advance (PREREG.md section 4)."""
    d, e = abs(r["delta"]), r["delta_err"]
    if r["separated"] and d >= 2.0 and d > 3 * e:
        return "TIE: sectors separated, one cell shifts the log-odds by %.1f" % r["delta"]
    if r["mixed"] and abs(r["df_direct"]) < 0.1 and d < 3 * e + 0.5:
        return "NO TIE: sectors mix, the breaker moves the sheet indicator by %.2f" % r["df_direct"]
    return "INCONCLUSIVE"


def analyse_ties(d, verbose=True):
    zs = {}
    for p in sorted(glob.glob(os.path.join(d, "*.npz"))):
        z = dict(np.load(p, allow_pickle=False))
        if "dS" in z and "sector" in z:
            zs[(str(z["group"]), round(float(z["beta"]), 4), int(z["ell"]), int(z["sep"]), str(z["sector"]))] = z
    rows = []
    for (g, b, ell, sep, sec), z in sorted(zs.items()):
        if sec != "A" or (g, b, ell, sep, "B") not in zs:
            continue
        r = analyse_tie(z, zs[(g, b, ell, sep, "B")])
        rows.append(r)
        if verbose:
            print(f"tie {g} beta={b} ell={ell} sep={sep}: f(A) {r['A']['f'][0]:.2f}..{r['A']['f'][-1]:.2f}, f(B) {r['B']['f'][0]:.2f}..{r['B']['f'][-1]:.2f}, "
                  f"switches A/B {r['A']['switches']}/{r['B']['switches']}; TI A {r['A']['I']:+.2f}+-{r['A']['I_err']:.2f} B {r['B']['I']:+.2f}+-{r['B']['I_err']:.2f}; "
                  f"delta {r['delta']:+.2f}+-{r['delta_err']:.2f} (strength {r['tie_strength']:.2f}); {r['verdict']}")
    return rows
