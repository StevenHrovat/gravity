"""Analyse goodblock.py runs (PREREG.md in this folder): the anisotropic refit of the good-blocking effective action, the adjoint and
centre halves (sup/TV and linearised W1 forms), the content check, the gates, the deconfinement flags and the scaling check.

Usage: python analyse_refit.py RUNS/*.npz [--out SUMMARY.json] [--photon-gate]

Reuses (imported, read-only): Leg C's error and decision code (../../attempts/r3-blocked/analyse_blocked.py: block_means, jackknife,
decide, a_sqrt_sigma, pair enumeration for a regression check, the W1 constants K_F, K_T) and workstream A's sharpened adjoint W1
bracket (../c2a-adjoint/evaluate_adjoint.py: K_A). Definitions are fixed in PREREG.md; this docstring repeats them briefly.

Fits      SD (SU(2), U(1)): M[S,S] beta_S = c[S]; base S = {F_ts, F_ss, A_ts, A_ss} ({q1, q2} per class); extensions add spin3/2 (q3)
          per class, rect (pooled), or both. Z2: pseudo-likelihood, base {P_ts, P_ss}, extension + rect.
Split     flip of one link: t -> -t. Centre-blind (adjoint) part of a plaquette factor: b_A(c) (4t^2 - 1)/3 (U(1): q2 cos 2th); centre-
          charged part: b_F(c) t + b_T(c)(2t^3 - t) (q1 cos th + q3 cos 3th); rectangles centre-charged. Z2: everything centre-charged.
TV halves for a link z (temporal or spatial): a(z, lam) = sum_{i != z} tanh(S0_iz / 2) e^{lam d}, c(z, lam) the same with the
          centre-charged oscillations; S_iz sums the oscillations of the factors shared by i and z (one plaquette at most, of class ts or
          ss; rectangles). gamma_A = max_z a, gamma_C = max_z c; H_TV = gamma_A + gamma_C (limitDprime_of_halves needs H < 1).
W1 (lin.) a_W(z) = 3 (8/3) k_A sum_{p ni z} |b_A(p)|, c_W(z) = 3 sum_{p ni z} (k_F |b_F(p)| + k_T |b_T(p)|) + 90 k_F |b_R|; H_W = max a_W +
          max c_W; hi/lo from the constant brackets (k_A in [2 sqrt2/(15 pi), 1/(5 pi)], k_T in [0, 0.1443]). U(1): 2/pi per unit coupling.
Verdict   NOT_EXCLUDED if hi + 2 stat < 1, EXCLUDED if lo - 2 stat > 1, else UNDECIDED; base and every extension fit must agree.
Content   (SU(2)) fundamental and adjoint coarse plaquettes of BOTH plane classes > 3 errors, and the Creutz ratio of the half-block
          lattice chi = -ln(W22 W11 / (W21 W12)) (pooled planes) within [0.5, 1.5] of sigma (b a / 2)^2 with error <= 0.25.
          Otherwise "NO CONTENT": the point does not count.
"""

import argparse
import glob
import importlib.util
import json
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


AB = _load("analyse_blocked", os.path.join(HERE, "..", "..", "attempts", "r3-blocked", "analyse_blocked.py"))
EA = _load("evaluate_adjoint", os.path.join(HERE, "..", "c2a-adjoint", "evaluate_adjoint.py"))

K_F, K_T, K_A = AB.K_F, AB.K_T, EA.K_A
FITS = {"su2": {"base": [0, 1, 2, 3], "ext_T": [0, 1, 2, 3, 4, 5], "ext_R": [0, 1, 2, 3, 6], "ext_TR": [0, 1, 2, 3, 4, 5, 6]},
        "u1": {"base": [0, 1, 2, 3], "ext_T": [0, 1, 2, 3, 4, 5], "ext_R": [0, 1, 2, 3, 6], "ext_TR": [0, 1, 2, 3, 4, 5, 6]},
        "z2": {"base": [0, 1], "ext_R": [0, 1, 2]}}
NVEC = {"su2": 7, "u1": 7, "z2": 3}
PLAQ_PER_LINK = {"t": (6, 0), "s": (2, 4)}  # (ts, ss) plaquettes through a temporal / spatial link
CONTENT = {"nsig": 3.0, "ratio_lo": 0.5, "ratio_hi": 1.5, "max_err": 0.25}
PHOTON = {"beta": 1.1, "rel_tol": 0.15, "max_rise": 1.5, "level": 0.5}
Z2_GATE_BETA = 0.6
L_DECONF = 1.45
M_OVER_SQRT_SIGMA = (3.5, 3.75, 4.0)
W1_CEILING = 0.28
SCALING = {"pair": ((2.3, 8), (2.5, 16)), "bracket": (0.3, 1.0)}
T = np.linspace(-1, 1, 4001)
TH = np.linspace(-np.pi, np.pi, 4001)


# ---------------------------------------------------------------------------------------------------------------------------- tables

def pair_table_aniso(L=7):
    """For a temporal (key 't') and a spatial (key 's') link z: rows (n_ts, n_ss, n_R, dist) for every link i != z sharing a factor
    with z: the shared plaquettes by plane class (at most one in all), the shared 1x2 rectangles, and Leg C's distance (ceil of the
    l_inf distance of the link midpoints). Enumerated on a periodic L^4 lattice (L = 7: infinite volume)."""
    E = np.eye(4, dtype=int)

    def lk(x, mu):
        return (tuple(int(v) for v in np.asarray(x) % L), mu)

    facs = []
    for x in np.ndindex(*(L,) * 4):
        x = np.array(x)
        for mu in range(4):
            for nu in range(4):
                if nu == mu:
                    continue
                if mu < nu:
                    facs.append(("ts" if 0 in (mu, nu) else "ss", [lk(x, mu), lk(x + E[mu], nu), lk(x + E[nu], mu), lk(x, nu)]))
                facs.append(("R", [lk(x, mu), lk(x + E[mu], mu), lk(x + 2 * E[mu], nu), lk(x + E[mu] + E[nu], mu), lk(x + E[nu], mu),
                                   lk(x, nu)]))

    def mid(link):
        x, mu = link
        m = np.array(x, float)
        m[mu] += 0.5
        return m

    out = {}
    for key, mus in (("t", (0,)), ("s", (1, 2, 3))):
        tabs = []
        for mu in mus:
            z = lk((L // 2,) * 4, mu)
            acc = {}
            for kind, links in facs:
                if z in links:
                    for i in set(links) - {z}:
                        a = acc.setdefault(i, [0, 0, 0])
                        a[{"ts": 0, "ss": 1, "R": 2}[kind]] += 1
            rows = []
            for i, (nts, nss, nR) in acc.items():
                d = np.abs(mid(i) - mid(z))
                d = np.minimum(d, L - d)
                rows.append((nts, nss, nR, int(math.ceil(d.max() - 1e-9))))
            tabs.append(sorted(rows))
        assert all(t == tabs[0] for t in tabs)
        out[key] = tabs[0]
    return out


_PT = {}


def pairs_aniso():
    if not _PT:
        _PT.update(pair_table_aniso())
    return _PT


# ---------------------------------------------------------------------------------------------------------------------------- fits

def z2_fit_aniso(H, S, iters=100):
    """Pseudo-likelihood fit of Z2 couplings (P_ts, P_ss, rect)[S] from the joint histogram H (7, 5, 19) of (x_ts, x_ss, y)."""
    H = np.asarray(H, float)
    g = np.meshgrid(np.arange(-6, 7, 2), np.arange(-4, 5, 2), np.arange(-18, 19, 2), indexing="ij")
    F = np.stack(g)[list(S)].astype(float)
    n = H.sum()
    beta = np.zeros(len(S))
    for _ in range(iters):
        h = np.tensordot(beta, F, 1)
        th = np.tanh(h)
        gr = (H[None] * F * (1 - th)[None]).sum(axis=(1, 2, 3))
        Hs = -(H[None, None] * F[:, None] * F[None] * (1 - th * th)[None, None]).sum(axis=(2, 3, 4))
        step = np.linalg.solve(Hs - 1e-12 * n * np.eye(len(S)), -gr)
        beta = beta + np.clip(step, -1, 1)
        if np.abs(step).max() < 1e-12 or np.abs(beta).max() > 20:
            break
    return beta


def fit_vec(group, S, arrs, i):
    v = np.zeros(NVEC[group])
    if group == "z2":
        v[list(S)] = z2_fit_aniso(arrs[0][i], S)
    else:
        v[list(S)] = AB.sd_fit(arrs[0][i], arrs[1][i], S)
    return v


# ---------------------------------------------------------------------------------------------------------------------------- halves

def osc(y):
    return float(y.max() - y.min())


def split_osc(group, v):
    """(o_e[ts, ss], o_o[ts, ss], o_R): oscillations of the centre-blind and centre-charged plaquette parts per class, and of the rect."""
    if group == "su2":
        oe = [4 / 3 * abs(v[2 + c]) for c in (0, 1)]
        oo = [osc(v[c] * T + v[4 + c] * (2 * T ** 3 - T)) for c in (0, 1)]
        return oe, oo, 2 * abs(v[6])
    if group == "u1":
        oe = [2 * abs(v[2 + c]) for c in (0, 1)]
        oo = [osc(v[c] * np.cos(TH) + v[4 + c] * np.cos(3 * TH)) for c in (0, 1)]
        return oe, oo, 2 * abs(v[6])
    return [0.0, 0.0], [2 * abs(v[0]), 2 * abs(v[1])], 2 * abs(v[2])


def halves_tv(oe, oo, oR, lam=0.0):
    """(gamma_A, gamma_C): max over link types of the adjoint and centre columns."""
    P = pairs_aniso()
    ga = max(sum(math.tanh((a * oe[0] + b * oe[1]) / 2) * math.exp(lam * d) for a, b, r, d in P[z]) for z in P)
    gc = max(sum(math.tanh((a * oo[0] + b * oo[1] + r * oR) / 2) * math.exp(lam * d) for a, b, r, d in P[z]) for z in P)
    return ga, gc


def lam_star(oe, oo, oR):
    if sum(halves_tv(oe, oo, oR)) >= 1:
        return 0.0
    lo, hi = 0.0, 1.0
    while sum(halves_tv(oe, oo, oR, hi)) < 1 and hi < 100:
        hi *= 2
    for _ in range(40):
        m = (lo + hi) / 2
        lo, hi = (m, hi) if sum(halves_tv(oe, oo, oR, m)) < 1 else (lo, m)
    return lo


def yx_tv(oe, oo, oR):
    """Y/X in TV form: 1 / s*, s* the factor on the adjoint couplings at which gamma_A + gamma_C = 1 (inf if gamma_C >= 1)."""
    ga, gc = halves_tv(oe, oo, oR)
    if gc >= 1:
        return float("inf")
    if ga == 0:
        return 0.0
    lo, hi = 0.0, 1.0
    while halves_tv([x * hi for x in oe], oo, oR)[0] + gc < 1 and hi < 1e9:
        hi *= 2
    for _ in range(60):
        m = (lo + hi) / 2
        lo, hi = (m, hi) if halves_tv([x * m for x in oe], oo, oR)[0] + gc < 1 else (lo, m)
    return 1 / lo if lo > 0 else float("inf")


def halves_w(group, v):
    """(aW_hi, aW_lo, cW_hi, cW_lo), max over link types, linearised W1 constants."""
    av = np.abs(np.asarray(v, float))
    res = {"a_hi": [], "a_lo": [], "c_hi": [], "c_lo": []}
    for z, (nts, nss) in PLAQ_PER_LINK.items():
        n = (nts, nss)
        if group == "su2":
            adj = 3 * (8 / 3) * sum(n[c] * av[2 + c] for c in (0, 1))
            res["a_hi"].append(adj * K_A[1])
            res["a_lo"].append(adj * K_A[0])
            for key, kt in (("c_hi", K_T[1]), ("c_lo", K_T[0])):
                res[key].append(3 * sum(n[c] * (K_F * av[c] + kt * av[4 + c]) for c in (0, 1)) + 90 * K_F * av[6])
        elif group == "u1":
            a = 3 * (2 / np.pi) * sum(n[c] * av[2 + c] for c in (0, 1))
            cc = 3 * (2 / np.pi) * sum(n[c] * (av[c] + av[4 + c]) for c in (0, 1)) + 90 * (2 / np.pi) * av[6]
            res["a_hi"].append(a)
            res["a_lo"].append(a)
            res["c_hi"].append(cc)
            res["c_lo"].append(cc)
        else:
            cc = 3 * sum(n[c] * math.tanh(av[c]) for c in (0, 1)) + 90 * math.tanh(av[2])
            res["a_hi"].append(0.0)
            res["a_lo"].append(0.0)
            res["c_hi"].append(cc)
            res["c_lo"].append(cc)
    return tuple(max(res[k]) for k in ("a_hi", "a_lo", "c_hi", "c_lo"))


def quantities(group, v):
    oe, oo, oR = split_osc(group, v)
    a, c = halves_tv(oe, oo, oR)
    ah, al, ch, cl = halves_w(group, v)
    r = {"a_TV": a, "c_TV": c, "H_TV": a + c, "lam_H": lam_star(oe, oo, oR), "YX_TV": yx_tv(oe, oo, oR),
         "a_W_hi": ah, "a_W_lo": al, "c_W_hi": ch, "c_W_lo": cl, "H_W_hi": ah + ch, "H_W_lo": al + cl,
         "YX_W_hi": ah / (1 - ch) if ch < 1 else float("inf"), "YX_W_lo": al / (1 - cl) if cl < 1 else float("inf")}
    return r


CRITS = {"H_TV": ("H_TV", "H_TV"), "a_TV": ("a_TV", "a_TV"), "c_TV": ("c_TV", "c_TV"),
         "H_W": ("H_W_hi", "H_W_lo"), "a_W": ("a_W_hi", "a_W_lo"), "c_W": ("c_W_hi", "c_W_lo")}


def selftest_tables():
    """Regression against Leg C and workstream A: the class-resolved pair tables add up to Leg C's pair table, and for isotropic
    couplings the halves equal evaluate_adjoint.quantities. Returns (max difference, detail)."""
    P = pairs_aniso()
    ref = sorted(AB.pairs())
    ok_tab = all(sorted((a + b, r, d) for a, b, r, d in P[z]) == ref for z in P)
    dmax = 0.0
    rng = np.random.default_rng(5)
    for _ in range(5):
        bF, bA, bT, bR = rng.normal(scale=[0.05, 0.03, 0.01, 0.005])
        q = quantities("su2", [bF, bF, bA, bA, bT, bT, bR])
        e = EA.quantities("su2", [bF, bA, bT, bR])
        for k in ("a_TV", "c_TV", "H_TV", "a_W_hi", "a_W_lo", "c_W_hi", "c_W_lo", "H_W_hi", "H_W_lo"):
            dmax = max(dmax, abs(q[k] - e[k]))
        dmax = max(dmax, abs(q["lam_H"] - e["lam_H"]) * 1e-3)  # bisection tolerance
    return (0.0 if ok_tab else 1.0) + dmax, f"tables pooled = Leg C's: {ok_tab}; isotropic halves vs evaluate_adjoint: max {dmax:.1e}"


# ---------------------------------------------------------------------------------------------------------------------------- per run

def evaluate_run(path):
    d = np.load(path, allow_pickle=False)
    group = str(d["group"])
    beta = float(d["beta"])
    chains = int(d["chains"])
    blocks = [int(b) for b in d["blocks"]]
    asq = AB.a_sqrt_sigma(beta) if group == "su2" else None
    fits = FITS[group]
    data_b = ([AB.block_means(d["hist"].astype(float), chains)] if group == "z2"
              else [AB.block_means(d["M"], chains), AB.block_means(d["c"], chains)])
    obs_b = AB.block_means(d["obs"], chains)        # (nb, P, 5)
    loops_b = AB.block_means(d["loops"], chains)    # (nb, P, 2, 4, 2)
    out = {"file": os.path.basename(path), "group": group, "beta": beta, "N": int(d["N"]), "w": float(d["w"]), "chains": chains,
           "n_meas": int(d["n_done"]), "partial": int(d["partial"]), "a_sqrt_sigma": asq, "points": []}
    for i, b in enumerate(blocks):

        def func(*arrs, i=i):
            r = {}
            vals = {}
            for name, S in fits.items():
                v = fit_vec(group, S, arrs, i)
                vals[name] = v
                for j, x in enumerate(v):
                    r[f"{name}:b{j}"] = float(x)
                for k, x in quantities(group, v).items():
                    r[f"{name}:{k}"] = float(x)
            if group != "z2":
                M, c = arrs[0][i], arrs[1][i]
                S = fits["base"]
                for j in range(NVEC[group]):
                    if j not in S:
                        r[f"closure{j}"] = float((M[j, S] @ vals["base"][S] - c[j]) / c[j]) if c[j] != 0 else float("nan")
            return r

        full, err = AB.jackknife(data_b, func)

        def cfunc(o, lp, i=i, b=b):
            r = {f"obs{j}": float(o[i, j]) for j in range(5)}
            W = lp[i, :, :, 0].mean(axis=0)  # pooled fundamental loops (1,1), (2,2), (2,1), (1,2) of the half-block lattice
            Wa = lp[i, :, :, 1].mean(axis=0)
            q = W[1] * W[0] / (W[2] * W[3]) if min(W) > 0 else float("nan")
            r["chi"] = -math.log(q) if q > 0 else float("nan")
            fpool = (o[i, 0] + o[i, 1]) / 2
            apool = (o[i, 2] + o[i, 3]) / 2
            r["fund_pool"], r["adj_pool"] = float(fpool), float(apool)
            r["W22_half"], r["W22a_half"] = float(W[1]), float(Wa[1])
            r["retain_F"] = float(fpool / W[1]) if W[1] != 0 else float("nan")
            r["retain_A"] = float(apool / Wa[1]) if Wa[1] != 0 else float("nan")
            for cl in (0, 1):
                for j in range(4):
                    r[f"loop{cl}{j}"] = float(lp[i, cl, j, 0])
                    r[f"loopA{cl}{j}"] = float(lp[i, cl, j, 1])
            return r
        cf, ce = AB.jackknife([obs_b, loops_b], cfunc)
        L = b * asq[0] if asq else None
        pt = {"b": b, "coarse_side": int(d["N"]) // b, "L_sqrt_sigma": L, "fits": {}, "verdict": {},
              "obs": {k: (cf[k], ce[k]) for k in cf}}
        for name in fits:
            keys = sorted({k.split(":", 1)[1] for k in full if k.startswith(name + ":")})
            pt["fits"][name] = {k: (full[f"{name}:{k}"], err[f"{name}:{k}"]) for k in keys}
        pt["closure"] = {k: (full[k], err[k]) for k in full if k.startswith("closure")}
        names = list(fits)
        for crit, (hi, lo) in CRITS.items():
            vs = []
            for n in names:
                fv = pt["fits"][n]
                s = max(fv[hi][1], fv[lo][1])
                s = s if np.isfinite(s) else 0.0
                vs.append(AB.decide(fv[hi][0], fv[lo][0], s))
            pt["verdict"][crit] = {"per_fit": dict(zip(names, vs)), "verdict": vs[0] if all(x == vs[0] for x in vs) else "UNDECIDED",
                                   "value_hi": pt["fits"]["base"][hi][0], "value_lo": pt["fits"]["base"][lo][0],
                                   "stat": pt["fits"]["base"][hi][1]}
        pt["lam_H_min"] = min(pt["fits"][n]["lam_H"][0] for n in fits)
        pt["drift"] = drift(d["obs"], chains, i)
        if group == "su2":
            pt["content"] = content_check(pt, b, asq)
            pt["counts"] = pt["content"]["status"] == "PASS"
            pt["mL_band"] = [m * L for m in M_OVER_SQRT_SIGMA]
            pt["gap_consistent"] = pt["lam_H_min"] <= M_OVER_SQRT_SIGMA[2] * L
            bA = [pt["fits"]["base"][f"b{j}"] for j in (2, 3)]
            pt["below_W1_ceiling"] = all(abs(x) + 2 * e < W1_CEILING for x, e in bA)
        else:
            pt["content"], pt["counts"] = {"status": "n/a"}, True
        out["points"].append(pt)
    return out


def drift(obs, chains, i):
    """Thermalisation diagnostic (reported): pooled fundamental and adjoint coarse plaquettes, first half of the measurements against
    the second half, difference in combined errors (block means as in the main analysis, at least 10 blocks per half)."""
    n = obs.shape[0]
    out = {}
    for name, cols in (("fund", [0, 1]), ("adj", [2, 3])):
        x = obs[:, :, i, cols].mean(axis=-1)  # (n, B)
        hs = []
        for part in (x[: n // 2], x[n // 2:]):
            per = max(1, min(part.shape[0], math.ceil(10 / chains)))
            sz = part.shape[0] // per
            bm = part[: per * sz].reshape(per, sz, -1).mean(axis=1).ravel()
            hs.append((float(bm.mean()), float(bm.std(ddof=1) / math.sqrt(len(bm))) if len(bm) > 1 else float("nan")))
        e = math.hypot(hs[0][1], hs[1][1])
        out[name] = {"first": hs[0], "second": hs[1], "sigma": (hs[1][0] - hs[0][0]) / e if e > 0 else float("nan")}
    return out


def content_check(pt, b, asq):
    o = pt["obs"]
    res = {}
    for k, name in ((0, "fund_ts"), (1, "fund_ss"), (2, "adj_ts"), (3, "adj_ss")):
        x, e = o[f"obs{k}"]
        res[name] = {"value": x, "err": e, "resolved": bool(np.isfinite(e) and x > CONTENT["nsig"] * e)}
    chi, chie = o["chi"]
    s2 = (b / 2) ** 2 * asq[0] ** 2
    ratio = chi / s2 if np.isfinite(chi) else float("nan")
    rerr = math.hypot(chie / s2, ratio * 2 * asq[1] / asq[0]) if np.isfinite(ratio) and np.isfinite(chie) else float("nan")
    if not np.isfinite(ratio) or not np.isfinite(rerr) or rerr > CONTENT["max_err"]:
        cst = "NOT_RESOLVED"
    elif CONTENT["ratio_lo"] <= ratio <= CONTENT["ratio_hi"]:
        cst = "PASS"
    else:
        cst = "FAIL"
    res["creutz"] = {"chi": chi, "chi_err": chie, "ratio": ratio, "ratio_err": rerr, "status": cst}
    res["retain_F"], res["retain_A"] = o["retain_F"], o["retain_A"]
    plaq_ok = all(res[k]["resolved"] for k in ("fund_ts", "fund_ss", "adj_ts", "adj_ss"))
    res["status"] = "PASS" if plaq_ok and cst == "PASS" else "NO_CONTENT"
    res["missing"] = [k for k in ("fund_ts", "fund_ss", "adj_ts", "adj_ss") if not res[k]["resolved"]] + ([] if cst == "PASS" else [f"creutz {cst}"])
    return res


# ---------------------------------------------------------------------------------------------------------------------------- report

def fmt(x, e=None, p=3):
    if x is None or (isinstance(x, float) and not np.isfinite(x)):
        return "inf" if x == float("inf") else "n/a"
    return f"{x:.{p}g}" if e is None or not np.isfinite(e) else f"{x:.{p}g} +- {e:.2g}"


def print_run(r):
    print(f"=== {r['group']} beta={r['beta']} N={r['N']} w={r['w']} chains={r['chains']} meas={r['n_meas']}{' (partial)' if r['partial'] else ''}")
    for p in r["points"]:
        bfit = p["fits"]["base"]
        L = f" L*sqrt(sigma)={p['L_sqrt_sigma']:.2f}" if p["L_sqrt_sigma"] else ""
        cpl = ", ".join(fmt(*bfit[f"b{j}"]) for j in range(NVEC[r["group"]]) if f"b{j}" in bfit)
        print(f"  b={p['b']:2d} (coarse {p['coarse_side']}^4){L} content {p['content']['status']}: base couplings [{cpl}]")
        o = p["obs"]
        print(f"      coarse plaq fund ts {fmt(*o['obs0'])} ss {fmt(*o['obs1'])}; adj ts {fmt(*o['obs2'])} ss {fmt(*o['obs3'])}; "
              f"half-block W22 fund {fmt(*o['W22_half'])} adj {fmt(*o['W22a_half'])}; retention F {fmt(*o['retain_F'])} A {fmt(*o['retain_A'])}")
        if r["group"] == "su2":
            c = p["content"]["creutz"]
            print(f"      Creutz (half block) chi {fmt(c['chi'], c['chi_err'])} ratio to sigma (b a/2)^2 {fmt(c['ratio'], c['ratio_err'])} "
                  f"{c['status']}; missing: {p['content']['missing'] or 'none'}")
        v = p["verdict"]
        print(f"      TV: a {fmt(*bfit['a_TV'])}  c {fmt(*bfit['c_TV'])}  H {fmt(*bfit['H_TV'])} -> H {v['H_TV']['verdict']}, a "
              f"{v['a_TV']['verdict']}, c {v['c_TV']['verdict']}; lam*_H {p['lam_H_min']:.3g}; Y/X TV {fmt(*bfit['YX_TV'])}")
        print(f"      W1 (lin.): a {fmt(bfit['a_W_hi'][0])}/{fmt(bfit['a_W_lo'][0])}  c {fmt(bfit['c_W_hi'][0])}/{fmt(bfit['c_W_lo'][0])}  "
              f"H {fmt(bfit['H_W_hi'][0])}/{fmt(bfit['H_W_lo'][0])} +- {fmt(bfit['H_W_hi'][1])} -> H {v['H_W']['verdict']}, a "
              f"{v['a_W']['verdict']}, c {v['c_W']['verdict']}; Y/X W {fmt(bfit['YX_W_lo'][0])}-{fmt(bfit['YX_W_hi'][0])}")
        dr = p["drift"]
        print(f"      drift (2nd half - 1st half of the measurements): fund {fmt(dr['fund']['sigma'])} sigma, adj {fmt(dr['adj']['sigma'])} sigma")
        if p["closure"]:
            print("      closure of the base fit: " + ", ".join(f"{k} {fmt(*x)}" for k, x in sorted(p["closure"].items())))


def photon_gate(runs):
    """U(1) Coulomb (beta = 1.1): H_TV, H_W and the centre half c_TV EXCLUDED at every b; q1 of both classes flat in b and at level."""
    res = {}
    for r in runs:
        if r["group"] != "u1" or abs(r["beta"] - PHOTON["beta"]) > 1e-9:
            continue
        win = all(p["verdict"][c]["verdict"] == "EXCLUDED" for p in r["points"] for c in ("H_TV", "H_W", "c_TV"))
        flat, flat_sym, level, q1 = True, True, True, {}
        for cl, name in ((0, "ts"), (1, "ss")):
            xs = sorted([(p["b"],) + tuple(p["fits"]["base"][f"b{cl}"]) for p in r["points"]])
            mean = float(np.mean([x for _, x, _ in xs]))
            # pre-registered rule (PREREG.md, photon gate item 2): no fall with b (each larger b keeps >= 85 % of every smaller b's
            # value, within 2 combined errors) and no runaway (largest / smallest <= 1.5); Leg C's symmetric rule is reported
            nofall = all(x2 >= (1 - PHOTON["rel_tol"]) * x1 - 2 * math.hypot(e1, e2)
                         for i1, (_, x1, e1) in enumerate(xs) for (_, x2, e2) in xs[i1 + 1:])
            vals = [x for _, x, _ in xs]
            bounded = min(vals) > 0 and max(vals) / min(vals) <= PHOTON["max_rise"]
            flat &= nofall and bounded
            flat_sym &= all(abs(x - mean) <= PHOTON["rel_tol"] * mean + 2 * e for _, x, e in xs)
            level &= mean >= PHOTON["level"] * r["beta"]
            q1[name] = {"by_b": xs, "mean": mean, "no_fall": nofall, "bounded": bounded}
        res[f"beta{r['beta']}_N{r['N']}"] = {"windows_excluded": win, "flat": flat, "flat_symmetric_LegC": flat_sym, "level": level,
                                             "q1": q1, "pass": bool(win and flat and level)}
    return res


def z2_gate(runs):
    res = {}
    for r in runs:
        if r["group"] == "z2" and abs(r["beta"] - Z2_GATE_BETA) < 1e-9:
            res[f"beta{r['beta']}_N{r['N']}"] = {"pass": all(p["verdict"][c]["verdict"] == "EXCLUDED" for p in r["points"]
                                                             for c in ("H_TV", "H_W")),
                                                 "by_b": [(p["b"], p["verdict"]["H_TV"]["verdict"], p["verdict"]["H_W"]["verdict"])
                                                          for p in r["points"]]}
    return res


def scaling_check(rows):
    (b1, n1), (b2, n2) = SCALING["pair"]
    r1 = [x for x in rows if abs(x["beta"] - b1) < 1e-9 and x["b"] == n1]
    r2 = [x for x in rows if abs(x["beta"] - b2) < 1e-9 and x["b"] == n2]
    if not r1 or not r2:
        return {"status": "N/A (missing run)"}
    r1, r2 = r1[0], r2[0]
    lo, hi = SCALING["bracket"]
    out = {"L": (r1["L"], r2["L"]), "items": {}}
    for k in ("fund_ts", "fund_ss", "adj_ts", "adj_ss", "bF_ts", "bF_ss", "bA_ts", "bA_ss"):
        (x1, e1), (x2, e2) = r1["q"][k], r2["q"][k]
        e = math.hypot(e1, e2)
        if not (np.isfinite(x1) and abs(x1) > 2 * e1):
            out["items"][k] = {"x": (x1, x2), "status": "n/a (not resolved at the reference)"}
            continue
        s = np.sign(x1)
        ok = lo * abs(x1) - 2 * e <= s * x2 <= hi * abs(x1) + 2 * e
        out["items"][k] = {"x": (x1, x2), "err": (e1, e2), "ratio": x2 / x1, "status": "consistent" if ok else "INCONSISTENT"}
    st = [v["status"] for v in out["items"].values()]
    out["status"] = ("INCONSISTENT" if "INCONSISTENT" in st else "CONSISTENT" if "consistent" in st else "N/A (nothing resolved)")
    return out


def summary(runs):
    out = {"gates": {"photon": photon_gate(runs), "z2": z2_gate(runs)}, "su2": [], "flags": []}
    print("\n=== gates")
    for k, v in out["gates"]["photon"].items():
        print(f"  photon {k}: {'PASS' if v['pass'] else 'FAIL'} (windows and centre half EXCLUDED at every b: {v['windows_excluded']}; "
              f"q1 no fall and bounded {v['flat']} (Leg C's symmetric flatness, reported: {v['flat_symmetric_LegC']}), level {v['level']}; q1 ts {[(b, round(x, 4), round(e, 4)) for b, x, e in v['q1']['ts']['by_b']]}, "
              f"ss {[(b, round(x, 4), round(e, 4)) for b, x, e in v['q1']['ss']['by_b']]})")
    for k, v in out["gates"]["z2"].items():
        print(f"  z2 deconfined {k}: {'PASS' if v['pass'] else 'FAIL'} {v['by_b']}")
    print("\n=== SU(2) points (counted = content PASS)")
    for r in sorted([r for r in runs if r["group"] == "su2"], key=lambda r: r["beta"]):
        for p in r["points"]:
            bf = p["fits"]["base"]
            row = {"beta": r["beta"], "N": r["N"], "b": p["b"], "L": p["L_sqrt_sigma"], "content": p["content"]["status"],
                   "missing": p["content"]["missing"], "counts": p["counts"],
                   **{f"v_{c}": p["verdict"][c]["verdict"] for c in CRITS},
                   "H_TV": bf["H_TV"][0], "a_TV": bf["a_TV"][0], "c_TV": bf["c_TV"][0], "H_W_hi": bf["H_W_hi"][0],
                   "YX_TV": bf["YX_TV"][0], "lam_H": p["lam_H_min"], "gap_consistent": p["gap_consistent"],
                   "below_W1_ceiling": p["below_W1_ceiling"], "retain_F": p["obs"]["retain_F"], "retain_A": p["obs"]["retain_A"],
                   "q": {"fund_ts": p["obs"]["obs0"], "fund_ss": p["obs"]["obs1"], "adj_ts": p["obs"]["obs2"], "adj_ss": p["obs"]["obs3"],
                         "bF_ts": bf["b0"], "bF_ss": bf["b1"], "bA_ts": bf["b2"], "bA_ss": bf["b3"]}}
            out["su2"].append(row)
            if row["L"] < L_DECONF and any(row[f"v_{c}"] == "NOT_EXCLUDED" for c in ("H_TV", "H_W")):
                out["flags"].append(("deconfinement false positive", r["beta"], round(row["L"], 3)))
            if any(abs(p["drift"][k]["sigma"]) > 3 for k in ("fund", "adj")):
                out["flags"].append(("thermalisation drift > 3 sigma (reported)", r["beta"], round(row["L"], 3)))
            if not row["gap_consistent"]:
                out["flags"].append(("dimension-swap inconsistency (fit artefact)", r["beta"], round(row["L"], 3)))
            if row["v_H_TV"] == "NOT_EXCLUDED":
                reading = "halves criterion holds on the fitted truncated action (D' via limitDprime_of_halves)"
            elif row["v_H_TV"] == "EXCLUDED" and row["v_H_W"] == "NOT_EXCLUDED":
                reading = "W1 window reached, sup window not"
            elif row["v_c_TV"] == "EXCLUDED":
                reading = "centre half alone >= 1: obstruction not adjoint"
            elif row["v_H_TV"] == "EXCLUDED":
                reading = "both forms EXCLUDED (see Y/X)" if row["v_H_W"] == "EXCLUDED" else "TV EXCLUDED, W1 undecided"
            else:
                reading = "undecided"
            row["reading"] = reading if row["counts"] else f"NO CONTENT (uncounted; would read: {reading})"
            print(f"  beta={r['beta']} b={p['b']:2d} L={row['L']:.2f} {row['content']:10s} H_TV {fmt(row['H_TV'])} ({row['v_H_TV']}; adj "
                  f"{fmt(row['a_TV'])}, centre {fmt(row['c_TV'])}) H_W {fmt(row['H_W_hi'])} ({row['v_H_W']}) Y/X TV {fmt(row['YX_TV'])} "
                  f"lam* {row['lam_H']:.3g}; retention F {fmt(*row['retain_F'])} A {fmt(*row['retain_A'])} -> {row['reading']}")
    out["scaling"] = scaling_check(out["su2"])
    print(f"\n=== scaling check {SCALING['pair']}: {out['scaling']['status']}")
    for k, v in out["scaling"].get("items", {}).items():
        print(f"  {k}: {v}")
    cnt = sorted([x for x in out["su2"] if x["counts"]], key=lambda x: x["L"])
    out["entry"] = {"first_NOT_EXCLUDED_TV": min([x["L"] for x in cnt if x["v_H_TV"] == "NOT_EXCLUDED"], default=None),
                    "first_NOT_EXCLUDED_W": min([x["L"] for x in cnt if x["v_H_W"] == "NOT_EXCLUDED"], default=None),
                    "counted": [(x["beta"], x["b"], round(x["L"], 3)) for x in cnt]}
    print(f"\n=== counted points {out['entry']['counted']}; first NOT_EXCLUDED: TV {out['entry']['first_NOT_EXCLUDED_TV']}, "
          f"W1 {out['entry']['first_NOT_EXCLUDED_W']}")
    print(f"=== flags: {out['flags'] or 'none'}")
    return out


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+")
    ap.add_argument("--out")
    ap.add_argument("--photon-gate", action="store_true", help="only the photon gate; prints PHOTON GATE PASSED / FAILED")
    ap.add_argument("--scaling-pair", help="pipeline test only: override the scaling pair, e.g. 2.3:2,2.5:4 (beta:b,beta:b)")
    a = ap.parse_args(argv)
    if a.scaling_pair:
        SCALING["pair"] = tuple((float(x.split(":")[0]), int(x.split(":")[1])) for x in a.scaling_pair.split(","))
    files = sorted({f for p in a.files for f in glob.glob(p)})
    runs = [evaluate_run(f) for f in files]
    for r in runs:
        print_run(r)
    if a.photon_gate:
        g = photon_gate(runs)
        ok = bool(g) and all(v["pass"] for v in g.values())
        for k, v in g.items():
            print(f"photon {k}: {v}")
        print("PHOTON GATE PASSED" if ok else "PHOTON GATE FAILED")
        return 0
    s = summary(runs)
    if a.out:
        json.dump({"runs": runs, "summary": s}, open(a.out, "w"), indent=1, default=float)
    return 0


if __name__ == "__main__":
    sys.exit(main())
