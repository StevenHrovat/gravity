"""One-box, worst-case-boundary instrument (c7b-onebox-num, PREREG.md): how much does the interior of a box of side ell feel a change of its
frozen boundary, as a function of depth, box size and the size of the changed boundary patch?

Reuses ../../../lattice/boundary.py unchanged (Box, boundary conditions, heat bath + overrelaxation on CPU and GPU, gauge tools) and
analyse_boundary.py (a sqrt(sigma), blocked errors, exponential fits). Nothing in lattice/ is modified (bytecode writing is switched off).

Subcommands
-----------
  run GROUP BETA ELL BG OUT.npz [--patch B] [--pert flip|gauge] [--chains 4] [--therm 200] [--meas 400] [--seed 1] [--cpu]
        BG: calm | typical | hot | twist | flux   (boundary.py's boundary conditions, same seed = same boundary)
        --patch B: on top of BG, change the boundary patch of side B at the centre of the face x = 0 (B >= ELL: the whole face).
          flip : SU(2) link times -1 (the centre element), U(1)/Z2 angle + pi        (a real change of boundary data)
          gauge: boundary data multiplied by a random gauge transformation at the boundary sites (CONTROL: not a change; the
                 influence on gauge-invariant interior observables must be zero within errors)
        Measures, per plane and depth d (distance of the nearest corner of the loop from the boundary), the mean and mean square of
        the 1x1 and 2x2 Wilson loops (gauge invariant).
  analyse DIR [--out F.json]    influence tables, decay fits, scaling with ell, surface-count estimate, verdicts (rules in PREREG.md)
  selftest                      pipeline checks (loops vs boundary.py, gauge invariance, pairing, gauge control)
  pilot [--jobs 4]              the CPU pilot (tiny boxes), then analyse
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
import analyse_boundary as ab  # noqa: E402

PLANES = bd.PLANES
SIZES = (1, 2)
GAMMA = 0.5          # PREREG.md: pass threshold for the surface-count estimate
TV_PER_SIGMA = 0.4   # Gaussian: total variation = 0.4 * (shift / sd) for small shifts


# ------------------------------------------------------------------------------------------------------------------ boundary changes

def patch_sites(box, b):
    """Sites (y, z, t) of the patch on the face x = 0: a b^3 cube at the face centre; b >= ell: the whole face (0..ell)."""
    ell = box.ell
    if b >= ell:
        return np.arange(0, ell + 1)
    c0 = (ell - b) // 2
    return np.arange(c0, c0 + b)


def apply_flip(group, U, box, b):
    """Centre flip of the tangential links (directions 1, 2, 3) at the sites of the patch on the face x = 0. U: list of host arrays."""
    r = patch_sites(box, b)
    ell = box.ell
    for mu in (1, 2, 3):
        rr = [r, r, r]
        rr[mu - 1] = r[r <= ell - 1]  # a link in direction mu starts at s_mu <= ell - 1
        ix = np.ix_(*rr)
        sl = (slice(None), 0) + ix
        if group == "su2":
            U[mu][sl] = -U[mu][sl]
        else:
            U[mu][sl] = np.angle(np.exp(1j * (U[mu][sl] + np.pi)))
            if group == "z2":
                U[mu][sl] = np.where(np.abs(U[mu][sl]) > 1.0, np.pi, 0.0)
    return U


def apply_gauge(group, U, box, B, rng):
    """CONTROL: gauge transformation g at the boundary sites (random, identity inside), applied to the frozen links only. The dynamic
    links touching a boundary site absorb it (integration variable), so the law of every gauge-invariant interior observable is unchanged."""
    n = (B,) + box.dims
    bnd = box.inbox & (box.sdepth == 0)
    if group == "su2":
        g = np.zeros(n + (4,))
        g[..., 0] = 1.0
        r = rng.normal(size=(B, int(bnd.sum()), 4))
        g[:, bnd] = r / np.linalg.norm(r, axis=-1, keepdims=True)
    elif group == "z2":
        g = np.zeros(n)
        g[:, bnd] = np.pi * rng.integers(0, 2, size=(B, int(bnd.sum())))
    else:
        g = np.zeros(n)
        g[:, bnd] = rng.uniform(-np.pi, np.pi, size=(B, int(bnd.sum())))
    ops = bd.make_ops(group, np)
    V = bd.gauge_transform(ops, U, g)
    for mu in range(4):
        fz = ~box.dyn[mu]
        U[mu][:, fz] = V[mu][:, fz]
    return U


# ------------------------------------------------------------------------------------------------------------------ measurement

class Meas:
    """Mean and mean square of the n x n Wilson loops by depth, per plane. Depth = smallest distance from the box boundary of the
    four corners (corners all inside the box; loops all of whose links are frozen are left out)."""

    def __init__(self, ops, box, B, sizes=SIZES):
        self.ops, self.box, self.B, self.sizes = ops, box, B, sizes
        xp = ops.xp
        sd = box.sdepth
        self.idx, self.cnt, self.nd = {}, {}, {}
        deps = {}
        for n in sizes:
            deps[n] = []
            for mu, nu in PLANES:
                cs = [sd, bd.roll_np(sd, mu, n), bd.roll_np(sd, nu, n), bd.roll_np(bd.roll_np(sd, mu, n), nu, n)]
                d = np.minimum.reduce(cs)
                anyd = np.zeros(box.dims, bool)
                for r in range(n):
                    for (a, b_, s0, s1) in ((mu, nu, r, 0), (mu, nu, r, n), (nu, mu, r, 0), (nu, mu, r, n)):
                        # link in direction a at base x + s0 e_a + s1 e_b
                        anyd |= np.roll(np.roll(box.dyn[a], -s0, axis=a), -s1, axis=b_)
                valid = (np.minimum.reduce([c >= 0 for c in cs])) & anyd
                deps[n].append(np.where(valid, d, -1))
            nd = int(max(d.max() for d in deps[n])) + 1
            self.nd[n] = nd
            self.idx[n], cnt = [], []
            for d in deps[n]:
                b_ = np.where(d >= 0, d, nd).reshape(-1)
                self.idx[n].append(xp.asarray((np.arange(B)[:, None] * (nd + 1) + b_[None, :]).reshape(-1)))
                cnt.append(np.bincount(b_, minlength=nd + 1)[:nd])
            self.cnt[n] = np.array(cnt)

    def loops(self, U, n):
        o = self.ops
        out = []
        for mu, nu in PLANES:
            Lm, Ln = U[mu], U[nu]
            for r in range(1, n):
                Lm = o.mul(Lm, bd.sh(U[mu], mu, r))
                Ln = o.mul(Ln, bd.sh(U[nu], nu, r))
            W = o.mul(o.mul(Lm, bd.sh(Ln, mu, n)), o.mul(o.dag(bd.sh(Lm, nu, n)), o.dag(Ln)))
            out.append(W)
        return out

    def __call__(self, U):
        xp = self.ops.xp
        res = {}
        for n in self.sizes:
            nd = self.nd[n]
            m, q, so, to = [], [], [], []
            for k, W in enumerate(self.loops(U, n)):
                v = self.ops.re(W)
                if n == 1 and self.ops.im(W) is not None:  # U(1): sin(theta_p), the observable linear in the field (the photon witness)
                    w = self.ops.im(W)
                    for acc, vals in ((so, w), (to, w * w)):
                        s_ = xp.bincount(self.idx[n][k], weights=vals.reshape(-1), minlength=self.B * (nd + 1))
                        acc.append(s_.reshape(self.B, nd + 1)[:, :nd] / xp.asarray(np.maximum(self.cnt[n][k], 1)))
                for acc, vals in ((m, v), (q, v * v)):
                    s = xp.bincount(self.idx[n][k], weights=vals.reshape(-1), minlength=self.B * (nd + 1))
                    acc.append(s.reshape(self.B, nd + 1)[:, :nd] / xp.asarray(np.maximum(self.cnt[n][k], 1)))
            res[f"m{n}"] = xp.stack(m, axis=1)
            res[f"q{n}"] = xp.stack(q, axis=1)
            if so:
                res["so1"], res["to1"] = xp.stack(so, axis=1), xp.stack(to, axis=1)
        return {k: bd.to_host(v) for k, v in res.items()}


# ------------------------------------------------------------------------------------------------------------------ run

def run(a):
    gpu = not a.cpu
    xp = bd.get_xp(gpu)
    box = bd.Box(a.ell)
    B = a.chains
    ops = bd.make_ops(a.group, xp)
    t0 = time.time()
    U = bd.initial_links(a.group, box, a.bg, B, a.seed, a.phi)
    if a.bg == "typical":  # periodic stage, then freeze its faces; same seed = same boundary for every patch variant
        upd = bd.make_updater(a.group, box, a.beta, U, a.seed, gpu)
        upd.set_dynamic([np.ones(box.dims, bool)] * 4)
        for _ in range(a.periodic_therm):
            upd.sweep(a.n_or)
        U = [bd.to_host(u).copy() for u in upd.links()]
    if a.patch > 0:
        if a.pert == "flip":
            U = apply_flip(a.group, U, box, a.patch)
        else:
            U = apply_gauge(a.group, U, box, B, np.random.default_rng(777 + a.seed))
    upd = bd.make_updater(a.group, box, a.beta, U, a.seed + 1, gpu)
    meas = Meas(ops, box, B)
    frozen0 = [bd.to_host(u)[:, ~box.dyn[mu]].copy() for mu, u in enumerate(upd.links())]
    for _ in range(a.therm):
        upd.sweep(a.n_or)
    rec = {}

    def save(m, partial):
        drift = max(float(np.max(np.abs(bd.to_host(u)[:, ~box.dyn[mu]] - frozen0[mu]))) for mu, u in enumerate(upd.links()))
        np.savez(a.out, group=a.group, beta=a.beta, ell=a.ell, bg=a.bg, patch=a.patch, pert=a.pert, seed=a.seed, chains=B,
                 therm=a.therm, n_or=a.n_or, every=a.every, backend="gpu" if gpu else "cpu", cnt1=meas.cnt[1], cnt2=meas.cnt[2],
                 seconds=time.time() - t0, partial=int(partial), n_done=m, frozen_drift=drift,
                 **{k: np.array(v[:m]) for k, v in rec.items()})
        return drift

    for m in range(a.meas):
        for _ in range(a.every):
            upd.sweep(a.n_or)
        for k, v in meas(upd.links()).items():
            rec.setdefault(k, []).append(v)
        if m % 100 == 0 and m:
            save(m, True)
    drift = save(a.meas, False)
    print(f"done {a.out} frozen drift {drift:.1e} in {time.time() - t0:.0f}s", flush=True)
    return 0 if drift == 0.0 else 1


# ------------------------------------------------------------------------------------------------------------------ analysis

def load_dir(d):
    runs = {}
    for p in sorted(glob.glob(os.path.join(d, "*.npz"))):
        z = dict(np.load(p, allow_pickle=False))
        if int(z.get("partial", 0)):
            continue
        key = (str(z["group"]), round(float(z["beta"]), 4), int(z["ell"]), str(z["bg"]), int(z["patch"]), str(z["pert"]))
        runs[key] = z
    return runs


def profile(z, n=1):
    """Pooled over planes: mean series (n_meas, B, nd) and the single-loop standard deviation by depth (nd,)."""
    c = z[f"cnt{n}"].astype(float)  # (6, nd)
    w = c[None, None]
    m = (z[f"m{n}"] * w).sum(axis=2) / w.sum(axis=2)
    q = (z[f"q{n}"] * w).sum(axis=2) / w.sum(axis=2)
    var = np.maximum(q.mean(axis=(0, 1)) - m.mean(axis=(0, 1)) ** 2, 1e-30)
    return m, np.sqrt(var)


def influence_odd(zp, zb):
    """U(1) only: shift of the mean sin(theta_p) (odd in the field), per plane; returns the plane with the largest shift/sd at each depth."""
    c = zp["cnt1"].astype(float)
    k = min(zp["so1"].shape[0], zb["so1"].shape[0])
    diff = zp["so1"][:k] - zb["so1"][:k]  # (n, B, 6, nd)
    n_, B_ = diff.shape[:2]
    d, e = ab.mean_err(diff, int(zp["chains"]))  # (6, nd)
    var = np.maximum(zb["to1"].mean(axis=(0, 1)) - zb["so1"].mean(axis=(0, 1)) ** 2, 1e-30)
    s = np.sqrt(var)
    pl = np.argmax(np.abs(d) / s, axis=0)
    ix = np.arange(d.shape[1])
    return d[pl, ix], e[pl, ix], s[pl, ix]


def influence(zp, zb, n=1):
    """Shift of the mean loop by depth, perturbed minus base, paired measurement by measurement (same seed => same boundary and
    random numbers, errors from blocks of the paired difference), in units of the single-loop standard deviation."""
    mp, sp = profile(zp, n)
    mb, sb = profile(zb, n)
    k = min(mp.shape[0], mb.shape[0])
    diff = mp[:k] - mb[:k]
    d, e = ab.mean_err(diff, int(zp["chains"]))
    return d, e, sb


def fit_decay(delta, err, d0=1):
    if len(delta) <= d0 + 1:
        return None, None
    xi, xe, idx = ab.decay(delta, err, d0)
    return xi, xe


def scaling_fit(ells, vals, errs):
    """Chi^2 of ln J against ell (exponential) and against ln ell (power law); returns (kappa, chi2_exp, p, chi2_pow)."""
    ells, vals, errs = map(np.asarray, (ells, vals, errs))
    ok = vals > 0
    if ok.sum() < 3:
        return None
    y = np.log(vals[ok])
    s = np.maximum(errs[ok] / vals[ok], 0.05)
    out = []
    for x in (ells[ok].astype(float), np.log(ells[ok].astype(float))):
        A = np.vstack([np.ones_like(x), x]).T
        W = 1 / s ** 2
        cov = np.linalg.inv(A.T @ (W[:, None] * A))
        c = cov @ (A.T @ (W * y))
        out.append((c[1], float(np.sum(W * (y - A @ c) ** 2))))
    return {"kappa": -out[0][0], "chi2_exp": out[0][1], "p": -out[1][0], "chi2_pow": out[1][1]}


def analyse(a):
    runs = load_dir(a.dir)
    res = {"groups": {}}
    keys = sorted({(k[0], k[1], k[2], k[3]) for k in runs})
    lines = []
    for (g, beta, ell, bg) in keys:
        base = runs.get((g, beta, ell, bg, 0, "flip"))
        if base is None:
            continue
        asq = ab.a_sqrt_sigma(beta)[0] if g == "su2" else None
        asq = asq[0] if asq else None
        for (g2, b2, l2, bg2, patch, pert), z in sorted(runs.items(), key=lambda kv: kv[0][4]):
            if (g2, b2, l2, bg2) != (g, beta, ell, bg) or patch == 0:
                continue
            ncell = (ell + 1) ** 3 if patch >= ell else patch ** 3
            for n in (1, 2):
                d, e, s = influence_odd(z, base) if (g == "u1" and n == 1) else influence(z, base, n)
                J, Je = np.abs(d) / s, e / s
                rec = {"group": g, "beta": beta, "ell": ell, "bg": bg, "patch": patch, "pert": pert, "loop": n,
                       "n_cells_patch": ncell, "depth": list(range(len(d))), "shift": d.tolist(), "err": e.tolist(),
                       "J": J.tolist(), "J_err": Je.tolist(), "sd_single": s.tolist()}
                if asq:
                    rec["depth_sqrt_sigma"] = [x * asq for x in range(len(d))]
                    xi, xe = fit_decay(d, e)
                    rec["xi_lat"], rec["xi_sqrt_sigma"] = xi, (xi * asq if xi else None)
                else:
                    rec["xi_lat"], _ = fit_decay(d, e)
                # surface-count estimate: 8 faces, per-cell influence from this patch by linear response, 0.4 per standard deviation
                nface = (ell + 1) ** 3
                rec["S_est"] = [8 * nface * TV_PER_SIGMA * float(j) / ncell for j in J]
                rec["S_est_err"] = [8 * nface * TV_PER_SIGMA * float(j) / ncell for j in Je]
                res["groups"].setdefault(f"{g} beta={beta} bg={bg}", []).append(rec)
    # extremes: different backgrounds against calm (same group, beta, ell)
    ext = []
    for (g, beta, ell, bg) in keys:
        calm = runs.get((g, beta, ell, "calm", 0, "flip"))
        z = runs.get((g, beta, ell, bg, 0, "flip"))
        if calm is None or z is None or bg == "calm":
            continue
        d, e, s = influence_odd(z, calm) if g == "u1" else influence(z, calm, 1)
        ext.append({"group": g, "beta": beta, "ell": ell, "bg": bg, "J": (np.abs(d) / s).tolist(), "J_err": (e / s).tolist(),
                    "shift": d.tolist(), "err": e.tolist()})
    res["extreme"] = ext
    # gauge control
    gc = []
    for k, z in runs.items():
        if k[5] == "gauge":
            base = runs.get((k[0], k[1], k[2], k[3], 0, "flip"))
            if base is None:
                continue
            d, e, s = influence_odd(z, base) if k[0] == "u1" else influence(z, base, 1)
            gc.append({"key": list(map(str, k)), "max_abs_over_err": float(np.max(np.abs(d) / np.maximum(e, 1e-300))),
                       "max_abs_shift": float(np.max(np.abs(d))), "shift": d.tolist(), "err": e.tolist()})
    res["gauge_control"] = gc
    res["verdicts"] = verdicts(res)
    if a.out:
        json.dump(res, open(a.out, "w"), indent=1)
    report(res)
    return 0


def centre_value(rec, key):
    """Value at the deepest depth with a resolved (>= 3 sigma) shift, else (None, upper limit at the deepest depth)."""
    return rec[key][-1]


def verdicts(res):
    """Rules of PREREG.md, section 'Verdict rules'. Per (group, beta, bg-family): look at the full-face patch and at the largest
    resolved small patch, at the centre depth, across ell."""
    out = {}
    fam = {}
    for lab, recs in res["groups"].items():
        for r in recs:
            if r["loop"] != 1:
                continue
            fam.setdefault((r["group"], r["beta"], r["bg"], r["pert"]), {}).setdefault(r["ell"], []).append(r)
    for (g, beta, bg, pert), per_ell in sorted(fam.items()):
        if pert == "gauge":
            continue
        ells = sorted(per_ell)
        S, Se, Jc, Jce = [], [], [], []
        for ell in ells:
            best = None
            for r in per_ell[ell]:  # smallest patch whose centre shift is resolved at >= 3 sigma gives the least screened estimate
                j, je = r["J"][-1], r["J_err"][-1]
                if j > 3 * je and (best is None or r["n_cells_patch"] < best["n_cells_patch"]):
                    best = r
            if best is not None:
                S.append(best["S_est"][-1])
                Se.append(best["S_est_err"][-1])
                Jc.append(best["J"][-1])
                Jce.append(best["J_err"][-1])
            else:  # unresolved: upper limit from the largest patch (3 sigma)
                r = min(per_ell[ell], key=lambda r: r["n_cells_patch"])  # per-cell limits come from the smallest patch only
                S.append(None)
                Se.append(3 * r["S_est_err"][-1])
                Jc.append(None)
                Jce.append(3 * r["J_err"][-1])
        v = {"ells": ells, "S_est": S, "S_limit_or_err": Se, "J_centre": Jc}
        resolved = [s for s in S if s is not None]
        if len(resolved) == len(S) and len(S) >= 2:
            fit = scaling_fit(ells, Jc, Jce)
            v["fit"] = fit
            last, prev = S[-1], S[-2]
            if last > 1.0 or last >= prev:
                v["verdict"] = "FAIL-like"
            elif last <= GAMMA and last <= 0.5 * prev:
                v["verdict"] = "PASS-like"
            else:
                v["verdict"] = "INCONCLUSIVE"
        elif not resolved and len(S) >= 1:
            v["verdict"] = "PASS-like (upper limits only)" if max(Se) <= GAMMA else "INCONCLUSIVE (limits too weak)"
        else:
            v["verdict"] = "INCONCLUSIVE"
        out[f"{g} beta={beta} bg={bg}"] = v
    # extreme-pair rule E: centre influence of a whole-boundary pair (background versus calm), across ell
    ex = {}
    for e in res["extreme"]:
        ex.setdefault((e["group"], e["beta"], e["bg"]), {})[e["ell"]] = (e["J"][-1], e["J_err"][-1])
    for (g, beta, bg), per in sorted(ex.items()):
        ells = sorted(per)
        (jl, el), (jp, ep) = per[ells[-1]], (per[ells[-2]] if len(ells) > 1 else (None, None))
        fit = scaling_fit(ells, [per[x][0] for x in ells], [per[x][1] for x in ells]) if len(ells) >= 3 else None
        exp_better = fit is not None and fit["chi2_exp"] <= fit["chi2_pow"]
        pow_better = fit is not None and fit["chi2_pow"] < fit["chi2_exp"]
        # two sizes cannot separate an exponential from a power law (U(1): flux/l^2 falls 2.2x from l = 4 to 6): no PASS from the ratio alone
        if jl < 3 * el or (exp_better and jl <= 0.5 * jp):
            verd = "PASS-like"
        elif jl >= 0.1 and (jp is None or jl >= 0.5 * jp or pow_better):
            verd = "FAIL-like"
        else:
            verd = "INCONCLUSIVE"
        out[f"{g} beta={beta} bg={bg} [extreme pair vs calm]"] = {"ells": ells, "J_centre": [per[x][0] for x in ells], "verdict": verd}
    return out


def report(res):
    print("== gauge control (must be zero within errors) ==")
    for c in res["gauge_control"]:
        print(f"  {c['key']}: max |shift|/err = {c['max_abs_over_err']:.2f}, max |shift| = {c['max_abs_shift']:.2e}")
    print("== influence J(d) = |shift| / sd of one loop, whole-face flip and patches, 1x1 loops ==")
    for lab, recs in res["groups"].items():
        for r in recs:
            if r["loop"] == 1:
                print(f"  {lab} ell={r['ell']} patch={r['patch']} {r['pert']}: J(d) = " + " ".join(f"{x:.3f}" for x in r["J"]) +
                      f"  | S_est(centre)={r['S_est'][-1]:.3f}")
    print("== extremes vs calm ==")
    for e in res["extreme"]:
        print(f"  {e['group']} beta={e['beta']} ell={e['ell']} {e['bg']}: J(d) = " + " ".join(f"{x:.3f}" for x in e["J"]))
    print("== verdicts ==")
    for k, v in res["verdicts"].items():
        extra = f" S_est={[None if s is None else round(s, 3) for s in v['S_est']]}" if "S_est" in v else f" J_centre={[round(x, 3) for x in v['J_centre']]}"
        print(f"  {k}: {v['verdict']}  ells={v['ells']}{extra}")


# ------------------------------------------------------------------------------------------------------------------ selftest / pilot

def selftest(a):
    ok = True
    for group, beta in (("su2", 2.3), ("u1", 1.1), ("z2", 0.6)):
        box = bd.Box(5)
        B = 2
        ops = bd.make_ops(group, np)
        rng = np.random.default_rng(3)
        U = bd.initial_links(group, box, "hot", B, 5)
        for mu in range(4):  # randomise the dynamic links too
            if group == "su2":
                r = rng.normal(size=U[mu].shape)
                r /= np.linalg.norm(r, axis=-1, keepdims=True)
                U[mu] = np.where(box.dyn[mu][None, ..., None], r, U[mu])
            else:
                U[mu] = np.where(box.dyn[mu][None], rng.uniform(-np.pi, np.pi, U[mu].shape) if group == "u1" else np.pi * rng.integers(0, 2, U[mu].shape), U[mu])
        m = Meas(ops, box, B)
        r0 = m(U)
        # 1x1 loops against boundary.py
        r1 = bd.Measure(ops, box, B)(U)["plaq"]
        d1 = np.max(np.abs(r0["m1"] - r1))
        # gauge invariance under a random INTERIOR transformation, and under the boundary-site gauge control applied to the frozen
        # links with the dynamic links left alone is NOT an invariance of a fixed configuration (they absorb it in the integral)
        g = bd.random_gauge(group, box, B, rng)
        r2 = m(bd.gauge_transform(ops, U, g))
        d2 = max(np.max(np.abs(r0[k] - r2[k])) for k in r0)
        # patch bookkeeping: whole-face flip changes exactly the tangential links of face x = 0
        V = apply_flip(group, [u.copy() for u in U], box, 99)
        changed = [np.any(np.abs(V[mu] - U[mu]) > 1e-12, axis=(0,) + ((5,) if group == "su2" else ())) for mu in range(4)]
        n_ch = sum(int(c.sum()) for c in changed)
        want = 3 * 5 * 6 * 6  # links in directions 1, 2, 3 at x = 0: 5 * 6 * 6 per direction (s_mu <= ell - 1, others 0..ell)
        d3 = abs(n_ch - want)
        good = d1 < 1e-12 and d2 < 1e-12 and d3 == 0
        ok &= good
        print(f"{group}: loops vs boundary.py {d1:.1e}, interior gauge invariance {d2:.1e}, face-flip links {n_ch} (want {want}) -> {'ok' if good else 'FAIL'}")
    print("selftest", "OK" if ok else "FAIL")
    return 0 if ok else 1


PILOT = [  # (group, beta, ell, therm, meas, chains)
    ("su2", 2.3, 4, 100, 300, 4), ("su2", 2.3, 6, 80, 120, 4), ("su2", 0.8, 4, 60, 300, 4),     ("u1", 2.0, 4, 100, 300, 4), ("u1", 2.0, 6, 80, 150, 4), ("z2", 0.6, 4, 60, 300, 4), ("z2", 0.6, 6, 60, 150, 4),
    ("z2", 0.3, 4, 60, 300, 4), ("z2", 0.3, 6, 60, 150, 4),
]


def pilot_jobs(out):
    jobs = []
    for g, beta, ell, th, me, ch in PILOT:
        bgs = ("calm", "twist") if g == "z2" else ("calm", "typical") if g == "su2" else ("calm", "flux")
        for bg in bgs:
            variants = [(0, "flip"), (2, "flip"), (ell, "flip")] if ell == 4 else [(0, "flip"), (ell, "flip")] + ([(ell, "gauge")] if bg == "calm" else [])
            for patch, pert in variants:
                name = f"{g}_b{beta}_l{ell}_{bg}_p{patch}{'g' if pert == 'gauge' else ''}"
                jobs.append((name, ["run", g, str(beta), str(ell), bg, os.path.join(out, name + ".npz"), "--patch", str(patch), "--pert", pert,
                                    "--therm", str(th), "--meas", str(me), "--chains", str(ch), "--seed", "11", "--cpu",
                                    "--periodic-therm", "60"]))
    return jobs


def pilot(a):
    out = os.path.join(HERE, "pilot-runs")
    os.makedirs(out, exist_ok=True)
    env = dict(os.environ, CUDA_VISIBLE_DEVICES="-1")
    jobs = pilot_jobs(out)
    t0 = time.time()
    running = []
    while jobs or running:
        running = [(n, p) for n, p in running if p.poll() is None]
        while jobs and len(running) < a.jobs and time.time() - t0 < a.budget:
            n, args = jobs.pop(0)
            if os.path.exists(os.path.join(out, n + ".npz")):
                continue
            running.append((n, subprocess.Popen([sys.executable, "-B", os.path.abspath(__file__)] + args, env=env,
                                                stdout=open(os.path.join(out, n + ".log"), "w"), stderr=subprocess.STDOUT)))
        if time.time() - t0 >= a.budget:
            jobs = []
        time.sleep(1)
    print(f"pilot runs finished in {time.time() - t0:.0f}s")
    a.dir, a.out = out, os.path.join(HERE, "pilot-analysis.json")
    return analyse(a)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("group", choices=("su2", "u1", "z2"))
    r.add_argument("beta", type=float)
    r.add_argument("ell", type=int)
    r.add_argument("bg", choices=("calm", "typical", "hot", "flux", "twist"))
    r.add_argument("out")
    r.add_argument("--patch", type=int, default=0)
    r.add_argument("--pert", choices=("flip", "gauge"), default="flip")
    r.add_argument("--chains", type=int, default=4)
    r.add_argument("--therm", type=int, default=200)
    r.add_argument("--meas", type=int, default=400)
    r.add_argument("--seed", type=int, default=1)
    r.add_argument("--n-or", type=int, default=3)
    r.add_argument("--every", type=int, default=2)
    r.add_argument("--periodic-therm", type=int, default=300)
    r.add_argument("--phi", type=float, default=None)
    r.add_argument("--cpu", action="store_true")
    s = sub.add_parser("analyse")
    s.add_argument("dir")
    s.add_argument("--out", default=None)
    sub.add_parser("selftest")
    p = sub.add_parser("pilot")
    p.add_argument("--jobs", type=int, default=5)
    p.add_argument("--budget", type=float, default=1500, help="seconds after which no new job is started")
    a = ap.parse_args()
    return {"run": run, "analyse": analyse, "selftest": selftest, "pilot": pilot}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
