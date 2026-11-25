"""Small-torus check of F_e(L) > 2 c(L) in the cubic geometry (ONEBOX-CHECK.md section 8, pre-registered). CPU only.

SU(2) Wilson heat bath + over-relaxation on L^3 x T tori (even extents), per-plaquette couplings, snake for Z_tw/Z, cut-parameter
thermodynamic integration for G = Z(L)^2 / Z(2L).

Usage:
  py smalltorus.py sanity
  py smalltorus.py time                       # sweep cost per torus size
  py smalltorus.py unit                       # one full snake ensemble, L = 4, beta 2.3 (timed)
  py smalltorus.py run [--only L,beta]        # production, resumable (one json per ensemble in runs/smalltorus/)
  py smalltorus.py analyse
"""
import argparse
import json
import math
import os
import sys
import time

import numpy as np

CONJ = np.array([1.0, -1.0, -1.0, -1.0])
NTHERM, NMEAS, NBIN = 200, 2000, 40
OUT = "runs/smalltorus"


def qm(a, b):
    a0, a1, a2, a3 = a[..., 0], a[..., 1], a[..., 2], a[..., 3]
    b0, b1, b2, b3 = b[..., 0], b[..., 1], b[..., 2], b[..., 3]
    return np.stack([a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3, a0 * b1 + b0 * a1 - (a2 * b3 - a3 * b2),
                     a0 * b2 + b0 * a2 - (a3 * b1 - a1 * b3), a0 * b3 + b0 * a3 - (a1 * b2 - a2 * b1)], axis=-1)


def cj(a):
    return a * CONJ


class Lattice:
    """Sites (t, x, y, z), t in [0, T), spatial in [0, L); direction 0 = time."""

    def __init__(self, L, T):
        self.L, self.T = L, T
        assert L % 2 == 0 and T % 2 == 0
        self.shape = (T, L, L, L)
        self.N = T * L ** 3
        c = np.indices(self.shape).reshape(4, -1)
        self.coords = c
        idx = np.arange(self.N).reshape(self.shape)
        self.fwd = [np.roll(idx, -1, axis=mu).ravel() for mu in range(4)]
        self.bwd = [np.roll(idx, 1, axis=mu).ravel() for mu in range(4)]
        # parity classes per direction: sum of coordinates other than mu, mod 2
        self.classes = []
        for mu in range(4):
            par = (c.sum(axis=0) - c[mu]) % 2
            self.classes.append([np.nonzero(par == p)[0] for p in (0, 1)])

    def site(self, t, x, y, z):
        return ((t * self.L + x) * self.L + y) * self.L + z

    def cut_time_maps(self):
        """Time maps of the cut lattice (two L^4 halves, L = T/2): t = L-1 -> 0 and t = 2L-1 -> L."""
        Lh = self.T // 2
        idx = np.arange(self.N).reshape(self.shape)
        fcut = idx.copy()
        bcut = idx.copy()
        for tt in range(self.T):
            if tt < Lh:
                nt = (tt + 1) % Lh
                pt = (tt - 1) % Lh
            else:
                nt = Lh + (tt - Lh + 1) % Lh
                pt = Lh + (tt - Lh - 1) % Lh
            fcut[tt] = idx[nt]
            bcut[tt] = idx[pt]
        return fcut.ravel(), bcut.ravel()


def family(lat, a, b, coup, fa=None, ia=None):
    return dict(a=a, b=b, c=coup, fa=lat.fwd[a] if fa is None else fa, ia=lat.bwd[a] if ia is None else ia,
                fb=lat.fwd[b], ib=lat.bwd[b])


def standard_families(lat, beta):
    return [family(lat, a, b, np.full(lat.N, beta)) for a in range(4) for b in range(a + 1, 4)]


def snake_order(L):
    out = []
    for x in range(L):
        ys = range(L) if x % 2 == 0 else range(L - 1, -1, -1)
        out += [(x, y) for y in ys]
    return out


def snake_families(lat, beta, m, k=3):
    """Plane (0, k) at t = 0, x_k = 0: first m-1 plaquettes flipped, plaquette m removed (1-based m)."""
    fams = standard_families(lat, beta)
    order = snake_order(lat.L)
    f = [fm for fm in fams if fm["a"] == 0 and fm["b"] == k][0]
    c = f["c"].copy()
    for j, (x, y) in enumerate(order[:m - 1]):
        c[lat.site(0, x, y, 0)] = -beta
    x, y = order[m - 1]
    pm = lat.site(0, x, y, 0)
    c[pm] = 0.0
    f["c"] = c
    return fams, (0, k, pm)


def glue_families(lat, beta, alpha):
    fams = standard_families(lat, beta)
    Lh = lat.T // 2
    bd = np.isin(lat.coords[0], [Lh - 1, lat.T - 1])
    fcut, bcut = lat.cut_time_maps()
    extra = []
    for f in fams:
        if f["a"] == 0:
            c = f["c"].copy()
            c[bd] = (1 - alpha) * beta
            f["c"] = c
            cc = np.zeros(lat.N)
            cc[bd] = alpha * beta
            extra.append(family(lat, 0, f["b"], cc, fa=fcut, ia=bcut))
    return fams + extra, bd, extra


def staple(U, fams, mu, idx):
    A = np.zeros((len(idx), 4))
    for f in fams:
        a, b, c = f["a"], f["b"], f["c"]
        if a == mu:
            # role A at x: S = B C^ D^
            cx = c[idx]
            nz = cx != 0
            if np.any(nz):
                ii = idx[nz]
                S = qm(qm(U[b][f["fa"][ii]], cj(U[a][f["fb"][ii]])), cj(U[b][ii]))
                A[nz] += cx[nz, None] * S
            # role C at y = ib(x): S = B^ A^ D
            y = f["ib"][idx]
            cy = c[y]
            nz = cy != 0
            if np.any(nz):
                yy = y[nz]
                S = qm(qm(cj(U[b][f["fa"][yy]]), cj(U[a][yy])), U[b][yy])
                A[nz] += cy[nz, None] * S
        elif b == mu:
            # role B at y = ia(x): S = C^ D^ A
            y = f["ia"][idx]
            cy = c[y]
            nz = cy != 0
            if np.any(nz):
                yy = y[nz]
                S = qm(qm(cj(U[a][f["fb"][yy]]), cj(U[b][yy])), U[a][yy])
                A[nz] += cy[nz, None] * S
            # role D at x: S = C B^ A^
            cx = c[idx]
            nz = cx != 0
            if np.any(nz):
                ii = idx[nz]
                S = qm(qm(U[a][f["fb"][ii]], cj(U[b][f["fa"][ii]])), cj(U[a][ii]))
                A[nz] += cx[nz, None] * S
    return A


def sample_w0(k, rng):
    n = len(k)
    w0 = np.empty(n)
    todo = np.arange(n)
    while len(todo):
        kk = k[todo]
        big = kk >= 2.0
        acc = np.zeros(len(todo), bool)
        val = np.empty(len(todo))
        # Kennedy-Pendleton
        if np.any(big):
            kb = kk[big]
            r1, r2, r3, r4 = rng.random((4, len(kb)))
            x = -(np.log(1 - r1) + np.cos(2 * np.pi * r2) ** 2 * np.log(1 - r3)) / kb
            ok = r4 ** 2 <= 1 - x / 2
            val[big] = 1 - x
            acc[big] = ok
        # Creutz
        sm = ~big
        if np.any(sm):
            ks = np.maximum(kk[sm], 1e-12)
            u, v = rng.random((2, len(ks)))
            w = 1 + np.log1p(-u * (-np.expm1(-2 * ks))) / ks
            w = np.clip(w, -1, 1)
            ok = v <= np.sqrt(np.maximum(0, 1 - w * w))
            val[sm] = w
            acc[sm] = ok
        w0[todo[acc]] = val[acc]
        todo = todo[~acc]
    return w0


def heatbath(U, fams, lat, rng):
    for mu in range(4):
        for idx in lat.classes[mu]:
            A = staple(U, fams, mu, idx)
            k = np.linalg.norm(A, axis=1)
            Ah = A / np.maximum(k, 1e-300)[:, None]
            w0 = sample_w0(k, rng)
            v = rng.normal(size=(len(idx), 3))
            v /= np.linalg.norm(v, axis=1, keepdims=True)
            W = np.concatenate([w0[:, None], np.sqrt(np.maximum(0, 1 - w0 * w0))[:, None] * v], axis=1)
            U[mu][idx] = qm(W, cj(Ah))


def overrelax(U, fams, lat):
    for mu in range(4):
        for idx in lat.classes[mu]:
            A = staple(U, fams, mu, idx)
            k = np.linalg.norm(A, axis=1)
            Ah = A / np.maximum(k, 1e-300)[:, None]
            U[mu][idx] = qm(qm(cj(Ah), cj(U[mu][idx])), cj(Ah))


def renorm(U):
    for mu in range(4):
        U[mu] /= np.linalg.norm(U[mu], axis=1, keepdims=True)


def sweep(U, fams, lat, rng):
    heatbath(U, fams, lat, rng)
    overrelax(U, fams, lat)
    overrelax(U, fams, lat)


def plaq_q(U, f, sites):
    a, b = f["a"], f["b"]
    P = qm(qm(qm(U[a][sites], U[b][f["fa"][sites]]), cj(U[a][f["fb"][sites]])), cj(U[b][sites]))
    return P[:, 0]


def mean_plaq(U, lat):
    tot = 0.0
    alls = np.arange(lat.N)
    for f in standard_families(lat, 1.0):
        tot += plaq_q(U, f, alls).mean()
    return tot / 6


def cold(lat):
    U = np.zeros((4, lat.N, 4))
    U[..., 0] = 1.0
    return U


def jack_bins(x):
    x = np.asarray(x)
    b = x[: len(x) // NBIN * NBIN].reshape(NBIN, -1).mean(axis=1)
    return b


def run_ensemble(kind, L, T, beta, param, seed, nmeas=NMEAS, ntherm=NTHERM):
    lat = Lattice(L, T)
    rng = np.random.default_rng(seed)
    U = cold(lat)
    if kind == "snake":
        fams, (a, b, pm) = snake_families(lat, beta, param)
        fm = [f for f in fams if f["a"] == a and f["b"] == b][0]
        meas = lambda: plaq_q(U, fm, np.array([pm]))[0]
    elif kind == "glue":
        fams, bd, extra = glue_families(lat, beta, param)
        bsites = np.nonzero(bd)[0]
        glued = [f for f in fams[:6] if f["a"] == 0]

        def meas():
            qc = sum(plaq_q(U, f, bsites).sum() for f in extra)
            qg = sum(plaq_q(U, f, bsites).sum() for f in glued)
            return beta * (qc - qg)
    else:
        fams = standard_families(lat, beta)
        meas = lambda: mean_plaq(U, lat)
    t0 = time.time()
    for _ in range(ntherm):
        sweep(U, fams, lat, rng)
    renorm(U)
    xs = []
    for i in range(nmeas):
        sweep(U, fams, lat, rng)
        if i % 100 == 0:
            renorm(U)
        xs.append(meas())
    return np.array(xs), time.time() - t0, U


def fname(kind, L, T, beta, param):
    return os.path.join(OUT, f"{kind}_L{L}_T{T}_b{beta}_{param}.json")


def do_one(kind, L, T, beta, param, seed):
    fn = fname(kind, L, T, beta, param)
    if os.path.exists(fn):
        return json.load(open(fn))
    xs, dt, _ = run_ensemble(kind, L, T, beta, param, seed)
    rec = dict(kind=kind, L=L, T=T, beta=beta, param=param, seed=seed, seconds=dt, nmeas=len(xs))
    if kind == "snake":
        rec["bins_em"] = jack_bins(np.exp(-beta * xs)).tolist()
        rec["bins_ep"] = jack_bins(np.exp(beta * xs)).tolist()
        rec["q_mean"] = float(xs.mean())
    else:
        rec["bins"] = jack_bins(xs).tolist()
    os.makedirs(OUT, exist_ok=True)
    json.dump(rec, open(fn, "w"))
    return rec


def ensembles():
    out = []
    for beta in (2.3, 3.5):
        for L in (2, 4, 6):
            for T in (L, 2 * L):
                for m in range(1, L * L + 1):
                    out.append(("snake", L, T, beta, m))
            for j in range(9):
                out.append(("glue", L, 2 * L, beta, j / 8))
    return out


def seed_of(kind, L, T, beta, param):
    return abs(hash((kind, L, T, beta, round(float(param), 6)))) % (2 ** 31) if False else \
        int(1000003 * L + 7919 * T + 101 * int(beta * 10) + int(round(float(param) * 1000)) + (0 if kind == "snake" else 5 * 10 ** 6))


def cmd_sanity():
    lat = Lattice(4, 4)
    U = cold(lat)
    print("identity plaquette:", mean_plaq(U, lat))
    from scipy.special import iv
    for beta in (0.5, 1.0):
        xs, dt, _ = run_ensemble("plaq", 4, 4, beta, 0, 1, nmeas=300, ntherm=100)
        print(f"beta {beta}: <q> {xs.mean():.4f} +- {xs.std() / math.sqrt(len(xs)) * 3:.4f}  single-plaquette {iv(2, beta) / iv(1, beta):.4f}  ({dt:.1f}s)")
    xs, dt, _ = run_ensemble("plaq", 6, 6, 2.3, 0, 2, nmeas=300, ntherm=100)
    print(f"beta 2.3 on 6^4: <q> {xs.mean():.4f} (16^4 value 0.602) ({dt:.1f}s)")
    # gluing endpoints: at alpha = 1, the cut lattice; check the cut plaquettes equal plaquettes of independent halves
    lat8 = Lattice(4, 8)
    fams, bd, extra = glue_families(lat8, 2.3, 1.0)
    print("glue families:", len(fams), "boundary sites:", int(bd.sum()), "(expect", 2 * 4 ** 3, ")")


def cmd_time():
    for (L, T) in ((2, 2), (2, 4), (4, 4), (4, 8), (6, 6), (6, 12)):
        lat = Lattice(L, T)
        fams = standard_families(lat, 2.3)
        U = cold(lat)
        rng = np.random.default_rng(0)
        for _ in range(5):
            sweep(U, fams, lat, rng)
        n = 20 if L < 6 else 10
        t0 = time.time()
        for _ in range(n):
            sweep(U, fams, lat, rng)
        dt = (time.time() - t0) / n
        print(f"L {L} T {T}: {dt * 1000:.1f} ms per sweep", flush=True)


def cmd_unit():
    t0 = time.time()
    xs, dt, U = run_ensemble("snake", 4, 4, 2.3, 8, 12345)
    print(f"unit (snake L4 T4 beta2.3 m8): {dt:.1f} s for {NTHERM + NMEAS} sweeps; <q_m> {xs.mean():.3f}", flush=True)


def cmd_run(only):
    todo = ensembles()
    if only:
        Lo, bo = only.split(",")
        todo = [e for e in todo if e[1] == int(Lo) and e[3] == float(bo)]
    t0 = time.time()
    for i, (kind, L, T, beta, param) in enumerate(todo):
        rec = do_one(kind, L, T, beta, param, seed_of(kind, L, T, beta, param))
        print(f"[{i + 1}/{len(todo)}] {kind} L{L} T{T} b{beta} {param}: {rec['seconds']:.1f}s (elapsed {time.time() - t0:.0f}s)", flush=True)


def jk_stats(fn_of_bins, bins_list):
    """bins_list: list of arrays (NBIN,) per ensemble component; returns value and jackknife sigma of fn over leave-one-bin-out."""
    full = fn_of_bins([b.mean() for b in bins_list])
    n = NBIN
    jk = []
    for i in range(n):
        jk.append(fn_of_bins([np.delete(b, i).mean() for b in bins_list]))
    jk = np.array(jk)
    return full, math.sqrt((n - 1) / n * np.sum((jk - jk.mean()) ** 2))


def cmd_analyse():
    res = {}
    for beta in (2.3, 3.5):
        for L in (2, 4, 6):
            r = {}
            ok = True
            for T in (L, 2 * L):
                lr, var = 0.0, 0.0
                for m in range(1, L * L + 1):
                    fn = fname("snake", L, T, beta, m)
                    if not os.path.exists(fn):
                        ok = False
                        break
                    rec = json.load(open(fn))
                    em, ep = np.array(rec["bins_em"]), np.array(rec["bins_ep"])
                    v, s = jk_stats(lambda x: math.log(x[0]) - math.log(x[1]), [em, ep])
                    lr += v
                    var += s * s
                r[T] = (lr, math.sqrt(var))
            if not ok:
                continue
            g_nodes, g_sig = [], []
            for j in range(9):
                fn = fname("glue", L, 2 * L, beta, j / 8)
                if not os.path.exists(fn):
                    ok = False
                    break
                b = np.array(json.load(open(fn))["bins"])
                g_nodes.append(b.mean())
                g_sig.append(b.std(ddof=1) / math.sqrt(NBIN))
            if not ok:
                continue
            g = np.array(g_nodes)
            gs = np.array(g_sig)
            wS = np.array([1, 4, 2, 4, 2, 4, 2, 4, 1]) / 24.0
            wT = np.array([0.5, 1, 1, 1, 1, 1, 1, 1, 0.5]) / 8.0
            logG = float(wS @ g)
            sG = math.sqrt(float((wS ** 2) @ (gs ** 2)) + (logG - float(wT @ g)) ** 2)
            lrL, slrL = r[L]
            lr2, slr2 = r[2 * L]
            rL, r2 = math.exp(lrL), math.exp(lr2)
            Fe = math.log((1 + rL) / (1 - rL)) if rL < 1 else float("inf")
            dFe = 2 * rL / (1 - rL * rL) * slrL if rL < 1 else float("inf")  # dF/dlog r = 2r/(1-r^2)
            c2 = logG + 2 * math.log1p(rL) - math.log(2) - math.log1p(r2)
            dc2_lrL = 2 * rL / (1 + rL)
            dc2_lr2 = r2 / (1 + r2)
            # D = 2 c_lb - F_e; log r_L enters both terms
            dD_lrL = dc2_lrL - 2 * rL / (1 - rL * rL)
            sD = math.sqrt(sG ** 2 + (dD_lrL * slrL) ** 2 + (dc2_lr2 * slr2) ** 2)
            D = c2 - Fe
            sDf = max(sD, 1.0)
            v = lambda s, z: "refuted" if D - z * s > 0 else "not refuted"
            res[f"{beta}_{L}"] = dict(beta=beta, L=L, log_r_L=lrL, sig_log_r_L=slrL, log_r_2L=lr2, sig_log_r_2L=slr2, r_L=rL, r_2L=r2,
                                      F_e=Fe, sig_F_e=dFe, logG=logG, sig_logG=sG, two_c_lb=c2, D=D, sig_D_stat=sD, sig_D=sDf,
                                      verdict95=v(sDf, 1.645), verdict99=v(sDf, 2.326),
                                      verdict95_stat=v(sD, 1.645), verdict99_stat=v(sD, 2.326))
            print(json.dumps(res[f"{beta}_{L}"]), flush=True)
    json.dump(res, open("runs/smalltorus_result.json", "w"), indent=1)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd")
    ap.add_argument("--only", default="")
    a = ap.parse_args()
    {"sanity": cmd_sanity, "time": cmd_time, "unit": cmd_unit, "analyse": cmd_analyse,
     "run": lambda: cmd_run(a.only)}[a.cmd]()
