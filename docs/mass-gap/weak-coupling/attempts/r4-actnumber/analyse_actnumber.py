"""Analysis of the act-number runs (PREREG.md in this folder is the reference for every rule below).

Per run: the unsubtracted zero-transverse-momentum correlators of the flux operators p_k (smearing levels k) and of the sign operator
s(t) = sign(p_top(t)) (SU(2), 2I, Z2); a variational step (generalised eigenvalues at t = 0, 1; analyse.best_projection, ours) on the
p_k; effective masses for a state running both ways round periodic time, cosh(E (T/2 - t)) (analyse.cosh_mass, ours); the plateau rule
of the TTL scan (analyse_plateau.plateau, ours: the smallest t >= 1 with m(t) agreeing with m(t+1) and m(t+2) within combined errors and
e(t) <= 0.25 m(t)); E = m(t*), z = L E. Jackknife over bins inside chains (chains x k bins, at least 20).
Counted point: plateau found, sheet check, drift check and autocorrelation check pass (PREREG.md "Counted points"). Upper estimate for
every point: z_up = L (m(2) + 2 e(2)) (effective masses of a positive-weight correlator approach E from above).

Usage: python analyse_actnumber.py RUN.npz [RUN.npz ...] [--out summary.json] [--pipeline]
"""

import argparse
import glob
import json
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
LATTICE = os.path.normpath(os.path.join(HERE, "..", "..", "..", "lattice"))
sys.path.insert(0, LATTICE)
from analyse import best_projection, cosh_mass  # noqa: E402  (ours, imported unchanged)
from analyse_plateau import plateau  # noqa: E402

TTL = os.path.normpath(os.path.join(HERE, "..", "..", "..", "results", "ttl_summary.json"))
SQRT_SIGMA_OVER_TC = 1.0 / 0.709  # 1/T_c in units of 1/sqrt(sigma) for SU(2) (T_c/sqrt(sigma) = 0.709; Lucini, Teper, Wenger 2004)
NG_CROSS = 1.58
F_STAR = math.log(1 + math.sqrt(2))  # self-dual point of F = -log tanh(F/2) (r3-monotone, r4-conjw C7)                   # Nambu-Goto z = sigma L^2 sqrt(1 - 2 pi / (3 sigma L^2)) = 1


def a_sqrt_sigma(beta):
    try:
        for r in json.load(open(TTL)):
            if abs(r["beta"] - beta) < 1e-9 and r.get("a_sqrt_sigma"):
                return tuple(r["a_sqrt_sigma"])
    except OSError:
        pass
    return None


def correlators(o, T):
    """o: (n, k, T) samples (complex allowed). C[t, i, j] = Re < o_i(t0 + t) conj o_j(t0) >, symmetrised, no vacuum subtraction."""
    n, k, _ = o.shape
    C = np.zeros((T // 2 + 1, k, k))
    for t in range(T // 2 + 1):
        C[t] = np.real(np.einsum("mis,mjs->ij", np.roll(o, -t, axis=2), np.conj(o))) / (n * T)
    return 0.5 * (C + np.transpose(C, (0, 2, 1)))


def rotor_corr(E1, t, T, nmax=12):
    """Correlator of exp(i phi) for a free quantum rotor with levels E_n = E1 n^2 on periodic time T (the U(1) flux tower: the photon's
    zero mode, E_n = e^2 n^2 / (2L)): sum_n exp(-E1 [n^2 (T - t) + (n + 1)^2 t]), up to normalisation."""
    n = np.arange(-nmax, nmax + 1)
    return np.sum(np.exp(-E1 * (n * n * (T - t) + (n + 1) ** 2 * t)))


def rotor_mass(c, t, T):
    """Solve c(t)/c(t+1) = R(t)/R(t+1) for E1 (bisection), R = rotor_corr."""
    r = c[t] / c[t + 1]
    if not np.isfinite(r) or r <= 1:
        return np.nan
    f = lambda E: rotor_corr(E, t, T) / rotor_corr(E, t + 1, T) - r
    lo, hi = 1e-6, 10.0
    if f(lo) > 0 or f(hi) < 0:
        return np.nan
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if f(mid) > 0:
            hi = mid
        else:
            lo = mid
    return 0.5 * (lo + hi)


def masses(o, T, project=True, rotor=False):
    C = correlators(o, T)
    if project and C.shape[1] > 1:
        v = best_projection(C)
        c = np.array([v @ C[t] @ v for t in range(T // 2 + 1)])
    else:
        c = C[:, -1, -1]
    mf = rotor_mass if rotor else cosh_mass
    return np.array([mf(c, t, T) for t in range(T // 2)])


def jk(samples, fn, B):
    """samples (B, n, ...): chain-major; jackknife over B x kpc contiguous bins inside chains."""
    n = samples.shape[1]
    kpc = max(1, math.ceil(20 / B))
    kpc = min(kpc, n)
    edges = np.linspace(0, n, kpc + 1).astype(int)
    full = fn(samples.reshape((-1,) + samples.shape[2:]))
    reps = []
    for b in range(B):
        for j in range(kpc):
            keep = np.ones((B, n), bool)
            keep[b, edges[j]:edges[j + 1]] = False
            reps.append(fn(samples[keep]))
    reps = np.array(reps)
    nb = len(reps)
    with np.errstate(invalid="ignore"):
        err = np.sqrt((nb - 1) / nb * np.nansum((reps - np.nanmean(reps, axis=0)) ** 2, axis=0))
    return full, err, kpc


def tau_int(x, c=6.0):
    """Integrated autocorrelation time (Sokal's automatic window), x 1D."""
    x = np.asarray(x, float) - np.mean(x)
    n = len(x)
    if n < 8 or np.var(x) == 0:
        return 0.5
    f = np.fft.rfft(x, 2 * n)
    acf = np.fft.irfft(f * np.conj(f))[:n]
    acf /= acf[0]
    tau = 0.5
    for w in range(1, n):
        tau += acf[w]
        if w >= c * tau:
            break
    return max(tau, 0.5)


def analyse_run(path):
    d = np.load(path, allow_pickle=False)
    group, beta, L, T = str(d["group"]), float(d["beta"]), int(d["L"]), int(d["T"])
    ops = d["ops"]  # (n, B, k, T)
    n, B = ops.shape[0], ops.shape[1]
    X = np.transpose(ops, (1, 0, 2, 3))  # (B, n, k, T)
    Ls = [int(v) for v in d["Ls"]] if "Ls" in d.files else [L, L, L]
    out = {"file": os.path.basename(path), "group": group, "beta": beta, "L": L, "Ls": Ls, "cubic": len(set(Ls)) == 1,
           "T": T, "plane": [int(v) for v in d["plane"]],
           "twisted": bool(int(d["twisted"])), "chains": B, "n_meas_per_chain": n, "partial": bool(int(d["partial"])),
           "levels": [int(v) for v in d["levels"]], "path": str(d["path"]), "seconds": float(d["seconds"])}
    out["plaquette"] = float(np.mean(d["plaq"]))
    asq = a_sqrt_sigma(beta) if group == "su2" or (group == "2i" and beta < 5) else None
    out["a_sqrt_sigma"] = asq
    out["L_sqrt_sigma"] = [L * asq[0], L * asq[1]] if asq else None
    if n < 8:
        out["verdict"] = "too few measurements"
        return out

    def fmass(x):
        return masses(x, T, project=True, rotor=(group == "u1"))
    m, e, kpc = jk(X, fmass, B)
    out["meff"] = [[float(a), float(b)] for a, b in zip(m, e)]
    tp = plateau(m, e)
    out["t_plateau"] = tp
    # sign operator
    if group != "u1":
        S = np.sign(np.real(X[:, :, -1:, :]))
        S[S == 0] = 1.0
        ms, es, _ = jk(S, lambda x: masses(x, T, project=False), B)
        out["meff_sign"] = [[float(a), float(b)] for a, b in zip(ms, es)]
        ts = plateau(ms, es)
        out["t_plateau_sign"] = ts
        out["E_sign"] = [float(ms[ts]), float(es[ts])] if ts is not None else None
        out["z_sign"] = [L * float(ms[ts]), L * float(es[ts])] if ts is not None else None
    # upper estimate from t = 2 (or the largest finite t <= 2)
    tu = 2 if len(m) > 2 and np.isfinite(m[2]) else (1 if np.isfinite(m[1]) else None)
    out["z_up"] = float(L * (m[tu] + 2 * e[tu])) if tu is not None else None
    # checks
    sheet = d["sheet"]  # (n, B, 2)
    dsb = (sheet[..., 0] - sheet[..., 1]).T  # (B, n)
    blk = dsb.reshape(B * kpc, -1) if n % kpc == 0 else dsb[:, : n // kpc * kpc].reshape(B * kpc, -1)
    dm, de = float(dsb.mean()), float(blk.mean(axis=1).std(ddof=1) / np.sqrt(blk.shape[0]))
    out["sheet_minus_bulk"] = [dm, de]
    out["sheet_ok"] = (not out["twisted"]) or abs(dm) <= 3 * de + 0.005
    xt = np.real(X[:, :, -1, :])  # top level
    lag = max(1, T // 4)
    series = (xt * np.roll(xt, -lag, axis=2)).mean(axis=2)  # (B, n): per-configuration C(T/4) estimate
    taus = [tau_int(series[b]) for b in range(B)]
    tau = float(np.max(taus))
    binlen = n / kpc
    out["tau_int_C(T/4)"] = tau
    out["bin_length"] = binlen
    out["tau_ok"] = binlen >= 4 * tau
    if tp is not None:
        E, dE = float(m[tp]), float(e[tp])
        out["E"] = [E, dE]
        out["z"] = [L * E, L * dE]
        h = n // 2
        if h >= 8:
            m1, e1, _ = jk(X[:, :h], fmass, B)
            m2, e2, _ = jk(X[:, h:], fmass, B)
            dd = abs(m1[tp] - m2[tp])
            out["drift"] = [float(m1[tp]), float(e1[tp]), float(m2[tp]), float(e2[tp])]
            out["drift_ok"] = bool(np.isfinite(dd) and dd <= 2 * np.hypot(e1[tp], e2[tp]))
        else:
            out["drift_ok"] = False
        if out.get("E_sign"):
            out["sign_consistent"] = bool(abs(out["E_sign"][0] - E) <= 2 * np.hypot(out["E_sign"][1], dE))
        out["counted"] = bool(out["sheet_ok"] and out["drift_ok"] and out["tau_ok"])
        out["verdict"] = "counted" if out["counted"] else "not counted (" + ", ".join(
            k for k in ("sheet_ok", "drift_ok", "tau_ok") if not out[k]) + ")"
    else:
        out["counted"] = False
        out["verdict"] = "no plateau"
    if group == "u1" and out.get("z"):
        out["alpha_R"] = [out["z"][0] / (2 * np.pi), out["z"][1] / (2 * np.pi)]
        out["alpha_bare"] = 1 / (4 * np.pi * beta)
    return out


# ---------------------------------------------------------------------------------------------------------------------------- readings

def curve(points):
    """points: list of (x, dx, z, dz) sorted by x (z > 0). Returns sampler of piecewise log-linear interpolants."""
    xs = np.array([p[0] for p in points])
    dxs = np.array([p[1] for p in points])
    zs = np.array([p[2] for p in points])
    dzs = np.array([p[3] for p in points])
    return xs, dxs, zs, dzs


def interp_logz(x, xs, zs):
    lx, lz = np.log(xs), np.log(np.maximum(zs, 1e-12))
    return np.exp(np.interp(np.log(x), lx, lz, left=np.nan, right=np.nan))


def mc_samples(xs, dxs, zs, dzs, ns=4000, seed=1):
    """Gaussian samples of (x, z); the a sqrt(sigma) error is common to all points of one beta (dx / x equal)."""
    rng = np.random.default_rng(seed)
    rel = (dxs / xs)[0] if len(xs) else 0.0
    sx = xs[None, :] * (1 + rel * rng.standard_normal((ns, 1)))
    sz = zs[None, :] + dzs[None, :] * rng.standard_normal((ns, len(zs)))
    return sx, np.maximum(sz, 1e-9)


def four_moves(cubes, boxes):
    """r4-conjw's split of one doubling into lengthening l = E(L,L,2L)/E(L,L,L) and widenings w_x = E(2L,L,2L)/E(L,L,2L),
    w_y = E(2L,2L,2L)/E(2L,L,2L), at the same beta (aE, so no lattice spacing); z(2L)/z(L) = 2 l w_x w_y. Counted runs only.
    W: l >= 2 and w >= (1 + delta)/2 with delta > 0 at 2 sigma; light: l = 2, w = 1/2. Margin delta = min(2 w_x - 1, 2 w_y - 1)."""
    def E(group, beta, Ls):
        for r in cubes + boxes:
            if r["group"] == group and abs(r["beta"] - beta) < 1e-9 and r["Ls"] == list(Ls) and r.get("counted") and r["plane"] == [0, 1]:
                return r["E"]
        return None
    out = []
    for r in boxes:
        Lx, Ly, Lz = r["Ls"]
        if not (Lx == Ly and Lz == 2 * Lx):
            continue
        g, b, L = r["group"], r["beta"], Lx
        e1, e2, e3, e4 = E(g, b, (L, L, L)), E(g, b, (L, L, 2 * L)), E(g, b, (2 * L, L, 2 * L)), E(g, b, (2 * L, 2 * L, 2 * L))
        ent = {"group": g, "beta": b, "L": L, "E": [e1, e2, e3, e4]}
        rs = []
        for num, den, key in ((e2, e1, "l"), (e3, e2, "w_x"), (e4, e3, "w_y")):
            if num and den:
                q = num[0] / den[0]
                ent[key] = [q, q * math.hypot(num[1] / num[0], den[1] / den[0])]
        if all(k in ent for k in ("w_x", "w_y")):
            ent["delta"] = min(2 * ent["w_x"][0] - 1, 2 * ent["w_y"][0] - 1)
            wl = min(ent["w_x"][0] - 2 * ent["w_x"][1], ent["w_y"][0] - 2 * ent["w_y"][1])
            l_ok = "l" in ent and ent["l"][0] + 2 * ent["l"][1] >= 2
            l_bad = "l" in ent and ent["l"][0] + 2 * ent["l"][1] < 2
            if l_ok and wl > 0.5:
                ent["verdict"] = "W HOLDS (widening above 1/2 and lengthening not below 2, at 2 sigma)"
            elif l_bad or min(ent["w_x"][0] + 2 * ent["w_x"][1], ent["w_y"][0] + 2 * ent["w_y"][1]) < 0.5:
                ent["verdict"] = "W FAILS (a widening below 1/2 or the lengthening below 2, at 2 sigma)"
            else:
                ent["verdict"] = "NOT RESOLVED"
            ent["delta_2sigma"] = 2 * wl - 1
        if g == "u1" and "l" in ent and "w_x" in ent and "w_y" in ent:
            # light: l = 2, w = 1/2, within 2 sigma plus a 10 % allowance for the box dependence of e_R^2 (Wilson action)
            okl = abs(ent["l"][0] - 2) <= 2 * ent["l"][1] + 0.2
            okw = all(abs(ent[k][0] - 0.5) <= 2 * ent[k][1] + 0.05 for k in ("w_x", "w_y"))
            ent["control"] = "LIGHT (l = 2, w = 1/2): PASSED" if (okl and okw) else "LIGHT: FAILED"
        if g == "2i":
            wx = ent.get("w_x")
            ent["control"] = ("PASSED (widening below 1/2 or E unresolved)" if (wx is None or wx[0] + 2 * wx[1] < 0.5)
                              else "FAILED (widening not below 1/2)")
        sym = E(g, b, (L, 2 * L, 2 * L))
        if sym and e3:
            ent["symmetry_pull"] = (sym[0] - e3[0]) / math.hypot(sym[1], e3[1])
        out.append(ent)
    return out


def readings(runs_all):
    R = {}
    boxes = [r for r in runs_all if not r["cubic"]]
    runs = [r for r in runs_all if r["cubic"]]
    R["four_moves"] = four_moves(runs, boxes)
    su2 = [r for r in runs if r["group"] == "su2" and r["twisted"] and r["plane"] == [0, 1] and r.get("counted") and r.get("L_sqrt_sigma")]
    by_beta = {}
    for r in su2:
        by_beta.setdefault(r["beta"], []).append((r["L_sqrt_sigma"][0], r["L_sqrt_sigma"][1], r["z"][0], r["z"][1], r["L"]))
    for b in by_beta:
        by_beta[b].sort()
    R["table"] = {str(b): [{"L": p[4], "L_sqrt_sigma": [p[0], p[1]], "z": [p[2], p[3]]} for p in v] for b, v in sorted(by_beta.items())}
    # (i) scaling check 2.4 vs 2.5 (and every other pair, reported)
    sc = []
    betas = sorted(by_beta)
    for i, b1 in enumerate(betas):
        for b2 in betas[i + 1:]:
            xs, dxs, zs, dzs = curve(by_beta[b1])
            for (x, dx, z, dz, L) in by_beta[b2]:
                if len(xs) < 2 or not (xs[0] <= x <= xs[-1]):
                    continue
                sx, sz = mc_samples(xs, dxs, zs, dzs)
                zi = np.array([interp_logz(x, sx[k], sz[k]) for k in range(len(sx))])
                zi = zi[np.isfinite(zi)]
                if zi.size < 100:
                    continue
                diff = z - zi.mean()
                err = math.hypot(dz, zi.std())
                sc.append({"betas": [b1, b2], "L": L, "L_sqrt_sigma": x, "z": [z, dz], "z_interp": [float(zi.mean()), float(zi.std())],
                           "pull": float(diff / err) if err > 0 else None})
    R["scaling"] = sc
    prim = [s for s in sc if s["betas"] == [2.4, 2.5] and s["pull"] is not None]
    if prim:
        pulls = np.abs([s["pull"] for s in prim])
        ok = (np.sum(pulls > 2) == 0) or (np.sum(pulls > 2) == 1 and np.max(pulls) <= 3 and len(prim) >= 4)
        R["scaling_verdict"] = "SCALING HOLDS" if ok else "SCALING VIOLATED (readings indicative only)"
    else:
        R["scaling_verdict"] = "NOT TESTED (no overlap)"
    # (ii) crossing of z = 1, (iii) growth per doubling, per beta
    R["crossing"], R["growth"] = {}, {}
    for b, pts in sorted(by_beta.items()):
        xs, dxs, zs, dzs = curve(pts)
        if len(xs) < 2:
            continue
        sx, sz = mc_samples(xs, dxs, zs, dzs, seed=int(b * 1000))
        cr = []
        for k in range(len(sx)):
            lz = np.log(sz[k])
            idx = np.where((lz[:-1] < 0) & (lz[1:] >= 0))[0]
            if idx.size:
                j = idx[0]
                fr = -lz[j] / (lz[j + 1] - lz[j])
                cr.append(math.exp(math.log(sx[k, j]) + fr * (math.log(sx[k, j + 1]) - math.log(sx[k, j]))))
        inv = []
        for k in range(len(sx)):
            lz = np.log(sz[k]) - math.log(F_STAR)
            idx = np.where((lz[:-1] < 0) & (lz[1:] >= 0))[0]
            if idx.size:
                j = idx[0]
                fr = -lz[j] / (lz[j + 1] - lz[j])
                inv.append(math.exp(math.log(sx[k, j]) + fr * (math.log(sx[k, j + 1]) - math.log(sx[k, j]))))
        R.setdefault("inversion_box_two_state", {})[str(b)] = (
            {"L_sqrt_sigma": [float(np.mean(inv)), float(np.std(inv))], "fraction_of_samples": len(inv) / len(sx)}
            if len(inv) > 0.5 * len(sx) else {"L_sqrt_sigma": None, "note": "z = F* not bracketed"})
        if len(cr) > 0.5 * len(sx):
            cr = np.array(cr)
            R["crossing"][str(b)] = {"L_star_sqrt_sigma": [float(cr.mean()), float(cr.std())], "fraction_of_samples": len(cr) / len(sx)}
        else:
            R["crossing"][str(b)] = {"L_star_sqrt_sigma": None, "note": "z = 1 not bracketed by counted points",
                                     "z_range": [float(zs.min()), float(zs.max())]}
        grid = [x for x in np.arange(0.5, 1.80001, 0.125) if xs[0] <= x and 2 * x <= xs[-1]]
        gro = []
        for x in grid:
            g = np.array([interp_logz(2 * x, sx[k], sz[k]) / interp_logz(x, sx[k], sz[k]) for k in range(len(sx))])
            g = g[np.isfinite(g)]
            if g.size > 100:
                gro.append({"L_sqrt_sigma": float(x), "g": [float(g.mean()), float(g.std())], "g_lo_2sigma": float(np.quantile(g, 0.0228))})
        root2 = []
        for x in np.arange(0.5, 3.6, 0.125):
            if xs[0] <= x and math.sqrt(2) * x <= xs[-1]:
                g = np.array([interp_logz(math.sqrt(2) * x, sx[k], sz[k]) / interp_logz(x, sx[k], sz[k]) for k in range(len(sx))])
                g = g[np.isfinite(g)]
                if g.size > 100:
                    root2.append({"L_sqrt_sigma": float(x), "g": [float(g.mean()), float(g.std())], "g_lo_2sigma": float(np.quantile(g, 0.0228))})
        entry = {"doubling": gro, "root2_step": root2}
        if gro:
            j = int(np.argmin([q["g"][0] for q in gro]))
            entry["g_min"] = gro[j]
            lows = [q["g_lo_2sigma"] for q in gro]
            if min(lows) > 1:
                entry["verdict"] = "GROWS WITH MARGIN"
            elif any(q["g"][0] + 2 * q["g"][1] < 1 for q in gro):
                entry["verdict"] = "FALLS SOMEWHERE"
            else:
                entry["verdict"] = "NEAR FIXED POINT (g consistent with 1 somewhere)"
            entry["delta_2sigma"] = float(min(lows) - 1)
        else:
            entry["verdict"] = "NOT TESTED (no doubling inside the counted range)"
        R["growth"][str(b)] = entry
        # (iv) large end, (v) small-L exponent
        big = [{"L_sqrt_sigma": float(x), "R_string": float(z / (x * x - math.pi / 3)), "dR": float(dz / (x * x - math.pi / 3)),
                "R_NG": float(z / (x * x * math.sqrt(max(1 - 2 * math.pi / (3 * x * x), 1e-9))))}
               for (x, dx, z, dz, L) in pts if x >= 2.5]
        R.setdefault("large_end", {})[str(b)] = big
        if len(xs) >= 2:
            R.setdefault("small_exponent", {})[str(b)] = {
                "between": [float(xs[0]), float(xs[1])],
                "d_log_z_d_log_L": float(math.log(zs[1] / zs[0]) / math.log(xs[1] / xs[0])) if zs[0] > 0 and zs[1] > 0 else None}
    # (vi) collapse test (added before data at the request of r4-minting: its assumption (U), one flow sigma)
    R["collapse"] = collapse(runs)
    # deconfinement expectation: no counted z - 2 sigma > 1 at L sqrt(sigma) <= 1.2
    viol = [(r["beta"], r["L"]) for r in su2 if r["L_sqrt_sigma"][0] <= 1.2 and r["z"][0] - 2 * r["z"][1] > 1]
    R["deconfinement_test"] = "CONSISTENT (z < 1 below L sqrt(sigma) = 1.2)" if not viol else f"ANOMALY at {viol}"
    # photon gate
    u1 = sorted([r for r in runs if r["group"] == "u1"], key=lambda r: r["L"])
    if u1:
        cnt = [r for r in u1 if r.get("counted")]
        res = {"points": [{"L": r["L"], "z": r.get("z"), "verdict": r["verdict"]} for r in u1]}
        if len(cnt) == len(u1) and len(cnt) >= 3:
            zz = np.array([r["z"][0] for r in cnt])
            dz = np.array([r["z"][1] for r in cnt])
            mean = float(zz.mean())
            flat = bool(np.all(np.abs(zz - mean) <= 0.15 * mean + 2 * dz))
            no_growth = bool(zz[-1] / zz[0] < 1.5)
            beta = cnt[0]["beta"]
            level = bool(0.3 <= mean * 2 * beta <= 3.0)
            res.update({"mean_z": mean, "two_pi_alpha_bare": 1 / (2 * beta), "alpha_R": mean / (2 * math.pi),
                        "alpha_bare": 1 / (4 * math.pi * beta), "flat": flat, "no_growth": no_growth, "level": level})
            res["verdict"] = "PHOTON GATE PASSED" if (flat and no_growth and level) else "PHOTON GATE FAILED"
        else:
            res["verdict"] = "PHOTON GATE FAILED (not every U(1) point counted)"
        R["photon_gate"] = res
    # deconfined controls
    for grp, beta in (("z2", 0.5), ("2i", 8.0)):
        rr = sorted([r for r in runs if r["group"] == grp and abs(r["beta"] - beta) < 1e-9], key=lambda r: r["L"])
        if not rr:
            continue
        ent = {"points": [{"L": r["L"], "z": r.get("z"), "z_up": r.get("z_up"), "verdict": r["verdict"]} for r in rr]}
        first, last = rr[0], rr[-1]
        zl = first["z"][0] if first.get("z") else None
        up_last = last.get("z_up")
        grow = (zl is not None and last.get("z") and last["z"][0] - 2 * last["z"][1] > zl + 2 * first["z"][1])
        if up_last is None:
            ent["verdict"] = "NOT RESOLVED"
        elif grow or up_last >= 1:
            ent["verdict"] = "CONTROL FAILED (no fall)"
        else:
            ent["verdict"] = "Z FALLS (control passed)"
        R[f"control_{grp}_{beta}"] = ent
    # symmetry control
    s12 = [r for r in runs if r["group"] == "su2" and r["plane"] == [1, 2] and r.get("z")]
    for r in s12:
        ref = [q for q in runs if q["group"] == "su2" and q["plane"] == [0, 1] and q["twisted"] and q["beta"] == r["beta"]
               and q["L"] == r["L"] and q.get("z")]
        if ref:
            q = ref[0]
            pull = (r["z"][0] - q["z"][0]) / math.hypot(r["z"][1], q["z"][1])
            R["symmetry_control"] = {"z_12": r["z"], "z_01": q["z"], "pull": pull,
                                     "verdict": "PASSED" if abs(pull) <= 2 else "FAILED (instrument asymmetry)"}
    # reported extras: periodic box, 2I below freezing
    ext = []
    for r in runs:
        if (r["group"] == "su2" and not r["twisted"]) or (r["group"] == "2i" and r["beta"] < 5):
            ref = [q for q in runs if q["group"] == "su2" and q["twisted"] and q["plane"] == [0, 1] and q["beta"] == r["beta"]
                   and q["L"] == r["L"] and q.get("z")]
            ext.append({"run": r["file"], "z": r.get("z"), "twisted_su2_same_beta_L": ref[0]["z"] if ref else None})
    R["extras"] = ext
    return R


def lattice_ssf(pts, ns=4000, seed=7):
    """pts: [(L, z, dz)] of one (group, beta), sorted by L. For every measured L with 2L <= L_max: per-sample u = z(L) and
    s = z(2L) (measured, or log-log interpolated in the lattice L between measured neighbours; no lattice spacing enters).
    Returns [(L, u_samples, s_samples)]."""
    Ls = np.array([p[0] for p in pts], float)
    zs = np.array([p[1] for p in pts])
    dzs = np.array([p[2] for p in pts])
    rng = np.random.default_rng(seed)
    S = np.maximum(zs[None, :] + dzs[None, :] * rng.standard_normal((ns, len(zs))), 1e-9)
    out = []
    for j, L in enumerate(Ls):
        if 2 * L > Ls[-1]:
            continue
        s2 = np.exp(np.array([np.interp(math.log(2 * L), np.log(Ls), np.log(S[k])) for k in range(ns)]))
        out.append((int(L), S[:, j], s2))
    return out


def _interp_sigma(u0, U, S):
    """log-log interpolation of one sample's (u, sigma) points at u0."""
    o = np.argsort(U)
    return math.exp(np.interp(math.log(u0), np.log(U[o]), np.log(S[o])))


def collapse(runs):
    """Collapse test of the one-flow assumption (U) of r4-minting: z(2L) against z(L) at several beta on one curve sigma(u).
    Pulls between beta curves; (a/L)^2 extrapolation at common u; min sigma(u)/u; controls U(1) (identity), Z2 and 2I (below)."""
    res = {}
    su2 = [r for r in runs if r["group"] == "su2" and r["twisted"] and r["plane"] == [0, 1] and r.get("counted")]
    curves = {}
    for b in sorted({r["beta"] for r in su2}):
        pts = sorted((r["L"], r["z"][0], r["z"][1]) for r in su2 if r["beta"] == b)
        if len(pts) >= 2:
            c = lattice_ssf(pts, seed=int(b * 100))
            if c:
                curves[b] = c
    res["points"] = {}
    for b, c in curves.items():
        res["points"][str(b)] = [{"L": L, "u": [float(u.mean()), float(u.std())], "sigma": [float(s.mean()), float(s.std())],
                                  "sigma_over_u": [float((s / u).mean()), float((s / u).std())]} for (L, u, s) in c]
    pulls = []
    bs = sorted(curves)
    for i, b1 in enumerate(bs):
        for b2 in bs[i + 1:]:
            c1 = curves[b1]
            if len(c1) < 2:
                continue
            U1 = np.array([q[1] for q in c1]).T  # (ns, n1)
            S1 = np.array([q[2] for q in c1]).T
            lo, hi = U1.mean(axis=0).min(), U1.mean(axis=0).max()
            for (L2, u2, s2) in curves[b2]:
                if not (lo <= u2.mean() <= hi):
                    continue
                diff = np.array([s2[k] - _interp_sigma(u2[k], U1[k], S1[k]) for k in range(len(u2))])
                pulls.append({"betas": [b1, b2], "L2": L2, "u": float(u2.mean()), "pull": float(diff.mean() / diff.std())})
            # and the other direction (points of the coarse curve against the fine one)
            c2 = curves[b2]
            if len(c2) >= 2:
                U2 = np.array([q[1] for q in c2]).T
                S2 = np.array([q[2] for q in c2]).T
                lo2, hi2 = U2.mean(axis=0).min(), U2.mean(axis=0).max()
                for (L1, u1, s1) in c1:
                    if not (lo2 <= u1.mean() <= hi2):
                        continue
                    diff = np.array([s1[k] - _interp_sigma(u1[k], U2[k], S2[k]) for k in range(len(u1))])
                    pulls.append({"betas": [b2, b1], "L2": L1, "u": float(u1.mean()), "pull": float(diff.mean() / diff.std())})
    res["pulls"] = pulls
    if pulls:
        p = np.abs([q["pull"] for q in pulls])
        ok = np.sum(p > 2) == 0 or (np.sum(p > 2) == 1 and p.max() <= 3 and len(p) >= 5)
        res["verdict"] = ("COLLAPSE HOLDS" if ok else
                          "COLLAPSE FAILS (the one-flow reading fails in this scheme at these spacings, or cutoff effects exceed the errors)")
    else:
        res["verdict"] = "NOT TESTED (no two beta curves overlap in u)"
    grid = []
    rngs = {b: (min(q[1].mean() for q in c), max(q[1].mean() for q in c)) for b, c in curves.items() if len(c) >= 2}
    if len(rngs) >= 1:
        lo = min(v[0] for v in rngs.values())
        hi = max(v[1] for v in rngs.values())
        for u0 in np.exp(np.linspace(math.log(lo), math.log(hi), 9)):
            rows = []
            for b, c in curves.items():
                if b not in rngs or not (rngs[b][0] <= u0 <= rngs[b][1]):
                    continue
                Ls = np.array([q[0] for q in c], float)
                U = np.array([q[1] for q in c]).T
                S = np.array([q[2] for q in c]).T
                sig = np.array([_interp_sigma(u0, U[k], S[k]) for k in range(U.shape[0])])
                Lu = float(np.mean([_interp_sigma(u0, U[k], Ls) for k in range(U.shape[0])]))
                rows.append((b, sig, Lu))
            ent = {"u": float(u0), "per_beta": [{"beta": b, "sigma": [float(sg.mean()), float(sg.std())], "L_lattice": Lu}
                                                 for (b, sg, Lu) in rows]}
            if len(rows) >= 2:
                X = np.array([[1.0, 1.0 / Lu ** 2] for (_, _, Lu) in rows])
                w = np.array([1.0 / max(sg.std(), 1e-12) for (_, sg, _) in rows])
                Ssm = np.array([sg for (_, sg, _) in rows]).T
                coef = np.array([np.linalg.lstsq(X * w[:, None], Ssm[k] * w, rcond=None)[0] for k in range(Ssm.shape[0])])
                sc = coef[:, 0]
                ent["sigma_continuum"] = [float(sc.mean()), float(sc.std())]
                ent["ratio_continuum"] = [float((sc / u0).mean()), float((sc / u0).std())]
                ent["n_beta"] = len(rows)
            grid.append(ent)
    res["continuum_grid"] = grid
    rat = [(g["ratio_continuum"], g["u"], g["n_beta"]) for g in grid if "ratio_continuum" in g]
    if rat:
        j = int(np.argmin([r[0][0] for r in rat]))
        res["min_sigma_over_u_continuum"] = {"value": rat[j][0], "at_u": rat[j][1], "n_beta": rat[j][2]}
    allr = [(q["sigma_over_u"], q["u"], b) for b, v in res["points"].items() for q in v]
    if allr:
        j = int(np.argmin([r[0][0] for r in allr]))
        res["min_sigma_over_u_lattice"] = {"value": allr[j][0], "at_u": allr[j][1], "beta": allr[j][2]}
    for grp in ("u1", "z2", "2i"):
        rr = [r for r in runs if r["group"] == grp and (grp != "2i" or r["beta"] > 5)]
        for b in sorted({r["beta"] for r in rr}):
            pts = sorted((r["L"], r["z"][0] if r.get("z") else None, r["z"][1] if r.get("z") else None, r.get("z_up"))
                         for r in rr if r["beta"] == b)
            ent = []
            for (L, z, dz, zu) in pts:
                for (L2, z2, dz2, zu2) in pts:
                    if L2 != 2 * L:
                        continue
                    if grp == "u1":
                        if z and z2:
                            q = z2 / z
                            er = q * math.hypot(dz / z, dz2 / z2)
                            ent.append({"L": L, "sigma_over_u": [q, er], "identity": bool(abs(q - 1) <= 0.15 + 2 * er)})
                    else:
                        below = ((z is not None and zu2 is not None and zu2 < z)
                                 or (z is not None and z2 is not None and z2 + 2 * dz2 < z - 2 * dz))
                        above = z is not None and z2 is not None and z2 - 2 * dz2 > z + 2 * dz
                        ent.append({"L": L, "u": z, "sigma": [z2, dz2] if z2 is not None else None, "sigma_up": zu2,
                                    "position": "below" if below else ("ABOVE" if above else "not resolved")})
            if grp == "u1":
                verdict = "NOT TESTED" if not ent else ("PASSED" if all(e["identity"] for e in ent) else "FAILED")
            elif not ent:
                verdict = "NOT TESTED"
            elif any(e["position"] == "ABOVE" for e in ent):
                verdict = "FAILED (sigma above the diagonal: growth in a deconfined theory)"
            elif all(e["position"] == "below" for e in ent):
                verdict = "PASSED (sigma below the diagonal)"
            else:
                verdict = "NOT RESOLVED (no growth, but not resolved below the diagonal)"
            res[f"control_{grp}_{b}"] = {"pairs": ent, "verdict": verdict}
    return res


def main():
    p = argparse.ArgumentParser()
    p.add_argument("files", nargs="+")
    p.add_argument("--out", default=None)
    p.add_argument("--photon-gate", action="store_true", help="only the U(1) runs; prints PHOTON GATE PASSED/FAILED")
    a = p.parse_args()
    files = []
    for f in a.files:
        files.extend(sorted(glob.glob(f)))
    runs = []
    for f in files:
        r = analyse_run(f)
        runs.append(r)
        zs = f"z = {r['z'][0]:.4f} +- {r['z'][1]:.4f}" if r.get("z") else "z = -"
        xs = f"L sqrt(sigma) = {r['L_sqrt_sigma'][0]:.2f}" if r.get("L_sqrt_sigma") else ""
        print(f"{r['file']:28s} {zs:28s} z_up {r.get('z_up') if r.get('z_up') is None else round(r['z_up'], 4)}  t* {r.get('t_plateau')}"
              f"  z_sign {None if not r.get('z_sign') else [round(v, 4) for v in r['z_sign']]}  tau {r.get('tau_int_C(T/4)', 0):.1f}/bin {r.get('bin_length', 0):.0f}  "
              f"sheet-bulk {r.get('sheet_minus_bulk')}  {xs}  [{r['verdict']}]", flush=True)
    R = readings(runs)
    if a.photon_gate:
        print(R.get("photon_gate", {}).get("verdict", "PHOTON GATE FAILED (no U(1) runs)"))
    else:
        print(json.dumps({k: v for k, v in R.items() if k not in ("table",)}, indent=1, default=float))
    if a.out:
        json.dump({"runs": runs, "readings": R}, open(a.out, "w"), indent=1, default=float)
    return 0


if __name__ == "__main__":
    sys.exit(main())
