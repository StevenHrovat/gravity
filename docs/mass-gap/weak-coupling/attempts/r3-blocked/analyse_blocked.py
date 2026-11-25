"""Analyse blocked.py runs (PREREG.md in this folder): the fitted blocked effective action, the window criteria, the controls, the
decision table, and the gradient-flow coupling.

Usage: python analyse_blocked.py RUNS/*.npz [--out SUMMARY.json] [--gate-photon]

Definitions (fixed in PREREG.md; change them there first)
-------------------------------------------------------
Errors        jackknife over blocks of measurements, blocks inside chains, at least 20 blocks per run (as ../../../lattice/
              analyse_boundary.py). 'stat' is the jackknife error; 'trunc' the largest change of the quantity when one extension
              coupling (spin3/2 or q3; rect) is added to the base fit, or both; 'err' = hypot(stat, trunc).
Fits          SU(2), U(1): solve M[S, S] beta_S = c[S] (Schwinger-Dyson); base S = {fund, adj} ({q1, q2}); extensions add spin3/2 (q3),
              rect, or both. Z2: pseudo-likelihood, base {plaq}, extension {plaq, rect}.
Closure       for the base fit, the SD identity of each unfitted basis function j: (M[j, S] beta_S - c_j) / c_j (0 if the truncated
              action were exact).
W1 (C)        linearised single-link W1 Dobrushin column sum (r2-curvature/NOTE.md 2.2-2.4), per neighbour the KR norm of the
              conditional law's derivative at the uniform point:
              SU(2) gamma = 18 (k_F |b_F| + (8/3) k_A |b_A| + k_T |b_T|) + 90 k_F |b_R|, k_F = 8/(9 pi) (exact), k_A in [0.0531, 0.0722]
                    (C's bracket), k_T in [0, 0.1443] (Poincare bound on the degree-3 harmonic, lower bound 0): gamma_hi uses the upper
                    constants, gamma_lo the lower ones;
              U(1)  gamma = 18 (2/pi)(|b_1| + |b_2| + |b_3|) + 90 (2/pi)|b_R|  (exact constants on the circle);
              Z2    gamma = 18 tanh|b_P| + 90 tanh|b_R|.
              90 = 18 rectangles x 5 other links. Inside the window: gamma < 1.
D'            r3-robust's criterion (r3-robust/NOTE.md 1, 4): D' = sum over links i != z of tanh(S_iz / 2), S_iz = n_P(i,z) o_P +
              n_R(i,z) o_R, o the oscillation (max - min over all configurations) of a plaquette / rectangle log-factor, n the number of
              such factors containing both links (enumerated: 18 plaquette pairs; with rectangles more). Inside: D' < 1. Weighted
              D'_lambda = sum tanh(S_iz / 2) exp(lambda dist(z, i)), dist = ceil(l_inf distance of link midpoints) in coarse units;
              reported: lambda* = sup{lambda : D'_lambda < 1} (min over the fits); the proven decay rate is lambda* / L.
BE            Bakry-Emery / Otto-Reznikoff (C 2.1), SU(2) base action only: (24 |b_F| + 76 |b_A|) / 2 < 1 (rigorous sufficient condition).
S'            B's soft-swap criterion (r2-coupling/NOTE.md 3.4): delta_X = 1 - (psi_min / psi_max)^2 = 1 - exp(-2 range(log psi_X)) per
              factor type; value = max over factor types X of sum over types Y of n(X meets Y) delta_Y, the counts n from enumeration
              (factors sharing at least one link, X itself excluded). Inside: value < 1.
Decision      per point, criterion and fit: NOT_EXCLUDED if value_hi + 2 stat < 1; EXCLUDED if value_lo - 2 stat > 1; else
              UNDECIDED. The point's verdict is NOT_EXCLUDED (EXCLUDED) only if the base fit and every extension fit say so (BE: base
              only); otherwise UNDECIDED. (Renamed after the round-3 review from INSIDE / OUTSIDE.) NOT_EXCLUDED means "not excluded
              on the truncated fit": the criteria are suprema over all configurations and all terms of the effective action, the fit
              is an equilibrium match of 2 to 4 terms, and omitted terms add non-negative oscillation, so the verdict is biased
              towards NOT_EXCLUDED (false positives). EXCLUDED is the robust direction: the fitted terms alone already break it.
Tables        D' and S' are evaluated with the infinite-volume pair/factor tables (enumerated on 7^4 and 6^4; identical for every
              torus side >= 5), which is the uniform-in-volume statement the theorems need; 'Dprime_torus' repeats D' with the
              table of the actual coarse torus (side N / b; on 3^4 and 4^4 wrap-around merges pairs), reported.
Signal        (SU(2), after the review) Creutz ratio chi(R0) = -ln(W(R0,R0) W(R0-1,R0-1) / (W(R0,R0-1) W(R0-1,R0))) of the flowed fine
              field at the blocking time, R0 = max(3, ceil(sqrt(8t))); the coarse loops of the deterministic block variable are
              exactly products of these fine loops, so this checks that the variable carries sigma at the smoothing scale. PASS if
              0.5 <= chi / (a sqrt(sigma))^2 <= 1.5 with error <= 0.25; otherwise FAIL or NOT_RESOLVED, and the point does not
              count. Separately: 'fundamental resolved' if the coarse plaquette exceeds 3 errors (at L sqrt(sigma) >= 3 it cannot:
              e^{-9} and below); an unresolved point speaks only through its adjoint channel.
Photon gate   (quantitative after the review) U(1) Coulomb, per (beta, f, noise): every b EXCLUDED on W1, D', S'; the base-fit q1
              coupling flat in b, |b_1(b) - mean| <= 0.15 mean + 2 err(b) for every b; and mean >= 0.5 beta_bare.
Volume        (after the review) runs at the same (group, beta) and different N: per (b, f, noise), b_F and b_A agree within 2
              combined errors.
GF coupling   g^2_GF(t) = (128 pi^2 / 9) t^2 E(t), E = 24 (1 - plaquette), alpha_GF = g^2 / (4 pi), at scale sqrt(8t) a sqrt(sigma).
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

MIN_BLOCKS = 20
K_F = 8 / (9 * np.pi)
K_A = (0.0531, 0.0722)
K_T = (0.0, math.sqrt(0.3125 / 15))  # ||(6t^2 - 1) s||_2 / sqrt(15); E[t^4 s^2] = 1/64, E[t^2 s^2] = 1/24, E[s^2] = 1/4 on S^3
FITS = {"su2": {"base": [0, 1], "ext_T": [0, 1, 2], "ext_R": [0, 1, 3], "ext_TR": [0, 1, 2, 3]},
        "u1": {"base": [0, 1], "ext_T": [0, 1, 2], "ext_R": [0, 1, 3], "ext_TR": [0, 1, 2, 3]},
        "z2": {"base": [0], "ext_R": [0, 1]}}
GATES = {"photon_beta": 1.1, "z2_deconfined_beta": 0.6, "u1_confined_beta": 0.9, "z2_confined_beta": 0.3, "primary_f": 0.5}
GF_NORM = 128 * np.pi ** 2 / 9


def a_sqrt_sigma(beta):
    try:
        from analyse_boundary import a_sqrt_sigma as asq
        return asq(beta)[0]
    except Exception:
        return None


# ---------------------------------------------------------------------------------------------------------------------------- counts

def factor_counts(L=6):
    """n(X meets Y) for X, Y in {plaquette, rectangle}: number of factors of type Y sharing at least one link with a given factor
    of type X (X itself excluded), by enumeration on a periodic L^4 lattice (maximum over orientations; L >= 5 is infinite volume)."""
    E = np.eye(4, dtype=int)

    def lk(x, mu):
        return (tuple(np.asarray(x) % L), mu)

    plaqs, rects = [], []
    for x in np.ndindex(*(L,) * 4):
        x = np.array(x)
        for mu in range(4):
            for nu in range(4):
                if nu == mu:
                    continue
                if mu < nu:
                    plaqs.append(frozenset([lk(x, mu), lk(x + E[mu], nu), lk(x + E[nu], mu), lk(x, nu)]))
                rects.append(frozenset([lk(x, mu), lk(x + E[mu], mu), lk(x + 2 * E[mu], nu), lk(x + E[mu] + E[nu], mu),
                                        lk(x + E[nu], mu), lk(x, nu)]))
    by_link = {}
    for kind, fs in (("P", plaqs), ("R", rects)):
        for i, f in enumerate(fs):
            for link in f:
                by_link.setdefault(link, []).append((kind, i))
    out = {}
    for kind, fs in (("P", plaqs), ("R", rects)):
        best = {"P": 0, "R": 0}
        for i, f in enumerate(fs[:12 if kind == "R" else 6]):  # the orientations at the origin
            met = {(k, j) for link in f for (k, j) in by_link[link]} - {(kind, i)}
            for k in ("P", "R"):
                best[k] = max(best[k], sum(1 for (kk, _) in met if kk == k))
        out[kind] = best
    return out


def pair_table(L=7):
    """For a link z: every other link i sharing a factor with it, as (n_P, n_R, dist): the number of plaquettes and of rectangles
    containing both, and dist = ceil(l_inf distance of the link midpoints, minimum image) (coarse units). By enumeration on a periodic
    L^4 lattice (L = 7: infinite volume; L = 3, 4: the small coarse tori, where wrap-around merges pairs); the same multiset for all
    four directions (asserted)."""
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
                    facs.append(("P", [lk(x, mu), lk(x + E[mu], nu), lk(x + E[nu], mu), lk(x, nu)]))
                facs.append(("R", [lk(x, mu), lk(x + E[mu], mu), lk(x + 2 * E[mu], nu), lk(x + E[mu] + E[nu], mu),
                                   lk(x + E[nu], mu), lk(x, nu)]))

    def mid(link):
        x, mu = link
        m = np.array(x, float)
        m[mu] += 0.5
        return m

    tables = []
    for mu in range(4):
        z = lk((L // 2,) * 4, mu)
        acc = {}
        for kind, links in facs:
            if z in links:
                for i in set(links) - {z}:
                    a = acc.setdefault(i, [0, 0])
                    a[0 if kind == "P" else 1] += 1
        rows = []
        for i, (nP, nR) in acc.items():
            d = np.abs(mid(i) - mid(z))
            d = np.minimum(d, L - d)
            rows.append((nP, nR, int(math.ceil(d.max() - 1e-9))))
        tables.append(sorted(rows))
    assert all(t == tables[0] for t in tables)
    return tables[0]


PAIRS = {}
INF_L = 7


def pairs(L=INF_L):
    L = INF_L if L is None or L >= 5 else L
    if L not in PAIRS:
        PAIRS[L] = pair_table(L)
    return PAIRS[L]


def dprime(oP, oR, lam=0.0, L=INF_L):
    """r3-robust's D'_lambda: sum over links i != z of tanh(S_iz / 2) exp(lambda dist(z, i)), S_iz = n_P o_P + n_R o_R (the
    oscillations of the factors through both links, worst case over configurations); pair table of torus side L."""
    return float(sum(math.tanh((nP * oP + nR * oR) / 2) * math.exp(lam * d) for nP, nR, d in pairs(L)))


def dprime_lambda_star(oP, oR):
    """Largest lambda (coarse units) with D'_lambda < 1; 0 if D'_0 >= 1."""
    if dprime(oP, oR) >= 1:
        return 0.0
    lo, hi = 0.0, 1.0
    while dprime(oP, oR, hi) < 1 and hi < 100:
        hi *= 2
    for _ in range(50):
        m = (lo + hi) / 2
        lo, hi = (m, hi) if dprime(oP, oR, m) < 1 else (lo, m)
    return lo


COUNTS = {}


def counts(L=6):
    L = 6 if L is None or L >= 5 else L
    if L not in COUNTS:
        COUNTS[L] = factor_counts(L)
    return COUNTS[L]


# ---------------------------------------------------------------------------------------------------------------------------- fits

def z2_fit(H, S, iters=100):
    """Pseudo-likelihood fit of Z2 couplings (plaq, rect)[S] from the joint histogram H (7, 19) of (sigma sum s_k, sigma sum r_j)."""
    H = np.asarray(H, float)
    x = np.arange(-6, 7, 2)[:, None] * np.ones((1, 19))
    y = np.ones((7, 1)) * np.arange(-18, 19, 2)[None, :]
    F = np.stack([x, y])[S]  # (k, 7, 19)
    n = H.sum()
    beta = np.zeros(len(S))
    for _ in range(iters):
        h = np.tensordot(beta, F, 1)
        th = np.tanh(h)
        g = (H[None] * F * (1 - th)[None]).sum(axis=(1, 2))  # gradient of sum n [h - log 2 cosh h], h = beta . F
        Hs = -(H[None, None] * F[:, None] * F[None] * (1 - th * th)[None, None]).sum(axis=(2, 3))
        step = np.linalg.solve(Hs - 1e-12 * n * np.eye(len(S)), -g)
        beta = beta + np.clip(step, -1, 1)
        if np.abs(step).max() < 1e-12:
            break
        if np.abs(beta).max() > 20:
            break
    return beta


def sd_fit(M, c, S):
    S = list(S)
    return np.linalg.solve(M[np.ix_(S, S)], c[S])


def range_su2(bF, bA, bT):
    t = np.linspace(-1, 1, 4001)
    f = bF * t + bA * (4 * t * t - 1) / 3 + bT * (2 * t ** 3 - t)
    return f.max() - f.min()


def range_u1(b1, b2, b3):
    th = np.linspace(-np.pi, np.pi, 4001)
    f = b1 * np.cos(th) + b2 * np.cos(2 * th) + b3 * np.cos(3 * th)
    return f.max() - f.min()


def criteria(group, b, Lc=None):
    """Window criteria for full coupling vector b (length 4 for su2/u1: base + spin3/2|q3 + rect; length 2 for z2: plaq, rect);
    D' and S' with the infinite-volume tables, 'Dprime_torus' with the table of the coarse torus side Lc."""
    n = counts()
    if group == "su2":
        bF, bA, bT, bR = (abs(x) for x in b)
        g_hi = 18 * (K_F * bF + (8 / 3) * K_A[1] * bA + K_T[1] * bT) + 90 * K_F * bR
        g_lo = 18 * (K_F * bF + (8 / 3) * K_A[0] * bA + K_T[0] * bT) + 90 * K_F * bR
        dP = 1 - math.exp(-2 * range_su2(b[0], b[1], b[2]))
        dR = 1 - math.exp(-4 * bR)
        be = (24 * bF + 76 * bA) / 2 if bT == 0 and bR == 0 else float("nan")
    elif group == "u1":
        g_hi = g_lo = 18 * (2 / np.pi) * (abs(b[0]) + abs(b[1]) + abs(b[2])) + 90 * (2 / np.pi) * abs(b[3])
        dP = 1 - math.exp(-2 * range_u1(b[0], b[1], b[2]))
        dR = 1 - math.exp(-4 * abs(b[3]))
        be = float("nan")
    else:
        g_hi = g_lo = 18 * math.tanh(abs(b[0])) + 90 * math.tanh(abs(b[1]))
        dP = 1 - math.exp(-4 * abs(b[0]))
        dR = 1 - math.exp(-4 * abs(b[1]))
        be = float("nan")
    if group == "su2":
        oP, oR = range_su2(b[0], b[1], b[2]), 2 * abs(b[3])
    elif group == "u1":
        oP, oR = range_u1(b[0], b[1], b[2]), 2 * abs(b[3])
    else:
        oP, oR = 2 * abs(b[0]), 2 * abs(b[1])
    dpr = dprime(oP, oR)
    lam = dprime_lambda_star(oP, oR)
    row_p = n["P"]["P"] * dP + n["P"]["R"] * dR
    row_r = n["R"]["P"] * dP + n["R"]["R"] * dR if dR > 0 else 0.0  # rectangle factors exist only with a rect coupling
    sp = max(row_p, row_r)
    return {"W1_hi": float(g_hi), "W1_lo": float(g_lo), "Sprime": float(sp), "BE": float(be), "Dprime": dpr, "Dprime_lam": lam,
            "Dprime_torus": dprime(oP, oR, 0.0, Lc)}


def full_vector(group, S, beta):
    k = 2 if group == "z2" else 4
    v = np.zeros(k)
    v[list(S)] = beta
    return v


# ---------------------------------------------------------------------------------------------------------------------------- errors

def block_means(x, chains):
    """x (n_meas, B, ...) -> block means (nblocks, ...), blocks inside chains, at least MIN_BLOCKS in total."""
    n = x.shape[0]
    per = min(max(1, math.ceil(MIN_BLOCKS / chains)), n)
    sz = n // per
    xb = x[:per * sz].reshape((per, sz) + x.shape[1:]).mean(axis=1)
    return xb.reshape((per * x.shape[1],) + x.shape[2:])


def jackknife(blocks, func):
    """func(mean over blocks) with jackknife error; func returns a dict of floats."""
    nb = blocks[0].shape[0]
    full = func(*[b.mean(axis=0) for b in blocks])
    tot = [b.sum(axis=0) for b in blocks]
    samples = [func(*[(t - b[i]) / (nb - 1) for t, b in zip(tot, blocks)]) for i in range(nb)]
    err = {}
    for k in full:
        v = np.array([s[k] for s in samples], dtype=float)
        err[k] = float(np.sqrt((nb - 1) / nb * ((v - v.mean()) ** 2).sum())) if np.all(np.isfinite(v)) else float("nan")
    return full, err


def decide(v_hi, v_lo, err):
    if not np.isfinite(v_hi):
        return "n/a"
    if v_hi + 2 * err < 1:
        return "NOT_EXCLUDED"
    if v_lo - 2 * err > 1:
        return "EXCLUDED"
    return "UNDECIDED"


# ---------------------------------------------------------------------------------------------------------------------------- per run

SIGNAL = {"ratio_lo": 0.5, "ratio_hi": 1.5, "max_err": 0.25}


def signal_check(cz_b, i, asq):
    """Creutz-ratio signal check of the flowed fine field at point i's flow time (see the module docstring)."""
    if cz_b is None or asq is None:
        return {"status": "NOT_MEASURED"}

    def func(w):
        W0, W1, W2, W3 = w[i]
        q = W1 * W0 / (W2 * W3) if min(W0, W1, W2, W3) > 0 else float("nan")
        chi = -math.log(q) if q > 0 else float("nan")
        return {"chi": chi, "ratio": chi / asq[0] ** 2}
    full, err = jackknife([cz_b], func)
    rerr = math.hypot(err["ratio"], full["ratio"] * 2 * asq[1] / asq[0]) if np.isfinite(full["ratio"]) else float("nan")
    if not np.isfinite(full["ratio"]) or not np.isfinite(rerr) or rerr > SIGNAL["max_err"]:
        st = "NOT_RESOLVED"
    elif SIGNAL["ratio_lo"] <= full["ratio"] <= SIGNAL["ratio_hi"]:
        st = "PASS"
    else:
        st = "FAIL"
    return {"chi": full["chi"], "chi_err": err["chi"], "ratio": full["ratio"], "ratio_err": rerr, "status": st}


GF_GRID = [0.5, 0.5]  # t_min, dt of the alpha_GF table (lattice units); pre-registered values, --gf-grid only for the pipeline test


def analyse_run(path):
    d = np.load(path, allow_pickle=False)
    group = str(d["group"])
    beta = float(d["beta"])
    chains = int(d["chains"])
    sched = d["schedule"]
    asq = a_sqrt_sigma(beta) if group == "su2" else None
    fits = FITS[group]
    N = int(d["N"])
    sched = np.array([tuple(p) + (0.0,) * (4 - len(p)) for p in sched])
    cz_b = block_means(d["creutz"], chains) if "creutz" in d.files and d["creutz"].size else None
    out = {"file": os.path.basename(path), "group": group, "beta": beta, "N": int(d["N"]), "chains": chains,
           "n_meas": int(d["n_done"]), "partial": int(d["partial"]), "a_sqrt_sigma": asq, "points": []}
    obs_b = block_means(d["obs"], chains)  # (nb, P, 3)
    if group == "z2":
        data_b = [block_means(d["hist"].astype(float), chains)]
    else:
        data_b = [block_means(d["M"], chains), block_means(d["c"], chains)]
    for i, (t, b, f, noise) in enumerate(sched):
        b = int(b)
        Lc = N // b

        def func(*arrs, i=i):
            r = {}
            vals = {}
            for name, S in fits.items():
                if group == "z2":
                    beta_S = z2_fit(arrs[0][i], S)
                else:
                    beta_S = sd_fit(arrs[0][i], arrs[1][i], S)
                v = full_vector(group, S, beta_S)
                vals[name] = v
                for j, x in enumerate(v):
                    r[f"{name}:b{j}"] = float(x)
                for k, x in criteria(group, v, Lc).items():
                    r[f"{name}:{k}"] = x
            if group != "z2":
                M, c = arrs[0][i], arrs[1][i]
                S = fits["base"]
                for j in range(4):
                    if j not in S:
                        r[f"closure{j}"] = float((M[j, S] @ vals["base"][S] - c[j]) / c[j]) if c[j] != 0 else float("nan")
            return r

        full, err = jackknife([x for x in data_b], func)
        ob, oe = jackknife([obs_b], lambda o, i=i: {f"obs{j}": float(o[i, j]) for j in range(3)})
        pt = {"t": float(t), "b": b, "f": float(f), "noise": float(noise), "coarse_side": Lc, "sqrt8t": float(math.sqrt(8 * t)),
              "L_sqrt_sigma": (b * asq[0]) if asq else None,
              "obs": [ob[f"obs{j}"] for j in range(3)], "obs_err": [oe[f"obs{j}"] for j in range(3)], "fits": {}, "decision": {}}
        for name in fits:
            k = 2 if group == "z2" else 4
            pt["fits"][name] = {"beta": [full[f"{name}:b{j}"] for j in range(k)], "stat": [err[f"{name}:b{j}"] for j in range(k)]}
            for crit in ("W1_hi", "W1_lo", "Sprime", "BE", "Dprime", "Dprime_lam", "Dprime_torus"):
                pt["fits"][name][crit] = (full[f"{name}:{crit}"], err[f"{name}:{crit}"])
        if group != "z2":
            pt["closure"] = {j: (full[f"closure{j}"], err[f"closure{j}"]) for j in range(4) if f"closure{j}" in full}
        base = pt["fits"]["base"]
        ext = [n for n in fits if n != "base"]
        trunc_b = [max(abs(pt["fits"][n]["beta"][j] - base["beta"][j]) for n in ext) for j in range(len(base["beta"]))]
        pt["beta"] = base["beta"][:2] if group != "z2" else base["beta"][:1]
        pt["beta_err"] = [math.hypot(base["stat"][j], trunc_b[j]) for j in range(len(pt["beta"]))]
        pt["beta_trunc"] = trunc_b[:len(pt["beta"])]
        for crit, lo in (("W1", "W1_lo"), ("Dprime", "Dprime"), ("Dprime_torus", "Dprime_torus"), ("Sprime", "Sprime"), ("BE", "BE")):
            hi = "W1_hi" if crit == "W1" else crit
            v_hi, s_hi = base[hi]
            v_lo, s_lo = base[lo]
            # the verdict must hold for the base fit and for every extension fit, each with its statistical error (an extension
            # can add factor types, e.g. rectangles for S', so a shift of the value is not an error bar); BE: base action only
            names = ["base"] if crit == "BE" else ["base"] + ext
            vs = [decide(pt["fits"][n][hi][0], pt["fits"][n][lo][0],
                         max(pt["fits"][n][hi][1], pt["fits"][n][lo][1]) if np.isfinite(pt["fits"][n][hi][1]) else 0.0) for n in names]
            verdict = vs[0] if all(v == vs[0] for v in vs) else "UNDECIDED"
            tr = max([abs(pt["fits"][n][hi][0] - v_hi) for n in names[1:]] or [0.0])
            pt["decision"][crit] = {"value_hi": v_hi, "value_lo": v_lo, "stat": s_hi, "trunc": tr, "err": s_hi,
                                    "per_fit": dict(zip(names, vs)), "verdict": verdict}
        pt["Dprime_lambda_star"] = min(pt["fits"][n]["Dprime_lam"][0] for n in fits)  # weighted D': rate in coarse units, min over fits
        pt["fund_resolved"] = bool(abs(pt["obs"][0]) > 3 * pt["obs_err"][0])
        pt["signal"] = signal_check(cz_b, i, asq) if group == "su2" else {"status": "n/a"}
        pt["counts"] = pt["signal"]["status"] in ("PASS", "n/a")
        if group == "su2":
            bF, bA = pt["beta"]
            pt["alpha_F"] = 1 / (np.pi * bF) if bF > 0 else float("inf")
            beq = bF + 8 / 3 * bA
            pt["alpha_eq"] = 1 / (np.pi * beq) if beq > 0 else float("inf")
        out["points"].append(pt)
    if group == "su2" and "flow_plaq" in d.files and d["flow_plaq"].size:
        out["gf"] = gf_table(d["flow_t"], d["flow_plaq"], chains, asq, GF_GRID[0], GF_GRID[1])
    return out


def gf_table(ft, fp, chains, asq, t_min=0.5, dt=0.5):
    """alpha_GF on a grid of flow times (every dt from t_min), with jackknife errors; monotonicity: successive differences."""
    ft = np.asarray(ft)
    grid = [j for j, t in enumerate(ft) if t >= t_min - 1e-9 and abs((t - t_min) / dt - round((t - t_min) / dt)) < 1e-6]
    pb = block_means(fp[..., grid], chains)  # (nb, n_grid)

    def func(p):
        r = {}
        for k, j in enumerate(grid):
            g2 = GF_NORM * ft[j] ** 2 * 24 * (1 - p[k])
            r[f"a{k}"] = g2 / (4 * np.pi)
            if k:
                r[f"d{k}"] = r[f"a{k}"] - r[f"a{k - 1}"]
        return r
    full, err = jackknife([pb], func)
    rows = [{"t": float(ft[j]), "sqrt8t": float(math.sqrt(8 * ft[j])), "scale_sqrt_sigma": float(math.sqrt(8 * ft[j]) * asq[0]) if asq else None,
             "alpha_GF": full[f"a{k}"], "err": err[f"a{k}"]} for k, j in enumerate(grid)]
    diffs = [(full[f"d{k}"], err[f"d{k}"]) for k in range(1, len(grid))]
    mono = all(dv > -2 * de for dv, de in diffs)
    strict = all(dv > 2 * de for dv, de in diffs)
    return {"rows": rows, "monotone_no_decrease_2sigma": mono, "strictly_increasing_2sigma": strict}


# ---------------------------------------------------------------------------------------------------------------------------- report

def fmt(v, e=None, p=4):
    if v is None or (isinstance(v, float) and not np.isfinite(v)):
        return "n/a"
    if e is None or not np.isfinite(e):
        return f"{v:.{p}g}"
    return f"{v:.{p}g} +- {e:.2g}"


def print_run(r):
    head = f"=== {r['group']} beta={r['beta']} N={r['N']} chains={r['chains']} meas={r['n_meas']}{' (partial)' if r['partial'] else ''}"
    if r["a_sqrt_sigma"]:
        head += f"  a*sqrt(sigma)={r['a_sqrt_sigma'][0]:.4f}"
    print(head)
    names = {"su2": "(b_F, b_A)", "u1": "(b_1, b_2)", "z2": "(b_P)"}[r["group"]]
    for p in r["points"]:
        L = f" L*sqrt(sigma)={p['L_sqrt_sigma']:.2f}" if p["L_sqrt_sigma"] else ""
        nz = f" noise beta_n={p['noise']:g}" if p["noise"] else ""
        print(f"  b={p['b']:2d} f={p['f']:.2f}{nz} t={p['t']:.3f}{L} coarse {p['coarse_side']}^4  coarse plaq {fmt(p['obs'][0], p['obs_err'][0])}  "
              f"{names} = {', '.join(fmt(v, e) for v, e in zip(p['beta'], p['beta_err']))} (trunc {', '.join(f'{x:.2g}' for x in p['beta_trunc'])})")
        ext = "; ".join(f"{n}: {np.round(f['beta'], 4).tolist()}" for n, f in p["fits"].items() if n != "base")
        print(f"      extensions {ext}")
        if "closure" in p:
            print(f"      closure of unfitted SD identities {', '.join(f'{j}: {fmt(v, e, 3)}' for j, (v, e) in p['closure'].items())}")
        dec = "; ".join(f"{c} {fmt(d['value_hi'], d['stat'], 3)}{'' if d['value_lo'] == d['value_hi'] else ' (lo ' + fmt(d['value_lo'], None, 3) + ')'}"
                        f" [ext spread {d['trunc']:.2g}] {d['verdict']}" for c, d in p["decision"].items() if d["verdict"] != "n/a")
        print(f"      {dec}")
        if r["group"] == "su2":
            sg = p["signal"]
            print(f"      signal check: {sg['status']}" + (f" (chi/sigma a^2 = {fmt(sg['ratio'], sg['ratio_err'], 3)})" if "ratio" in sg else "")
                  + f"; fundamental channel {'resolved' if p['fund_resolved'] else 'NOT resolved'}; D' on the {p['coarse_side']}^4 torus "
                  f"{fmt(p['decision']['Dprime_torus']['value_hi'], None, 3)}")
            print(f"      alpha_F = 1/(pi b_F) = {fmt(p['alpha_F'], None, 3)}; alpha_eq = 1/(pi (b_F + 8 b_A / 3)) = {fmt(p['alpha_eq'], None, 3)}")
    if "gf" in r:
        g = r["gf"]
        print("  gradient-flow coupling alpha_GF(sqrt(8t)):", ", ".join(
            f"{x['scale_sqrt_sigma']:.2f}/sqrt(sigma): {fmt(x['alpha_GF'], x['err'], 3)}" for x in g["rows"]))
        print(f"  monotone (no decrease beyond 2 sigma): {g['monotone_no_decrease_2sigma']}; strictly increasing: {g['strictly_increasing_2sigma']}")


PHOTON_FLAT = {"rel_tol": 0.15, "min_level": 0.5}
L_DECONF = 1.45  # 1 / T_c in units of 1 / sqrt(sigma), T_c / sqrt(sigma) ~ 0.69 for SU(2) (recalled)


def gate(runs, group, beta, f, want, noise=0.0):
    """All points of the given run(s) with smoothing f and noise: every window verdict must be `want` (EXCLUDED for the photon and
    deconfined Z2) on W1, D' and S'. Returns (status, details)."""
    rs = [r for r in runs if r["group"] == group and abs(r["beta"] - beta) < 1e-9]
    if not rs:
        return "missing", []
    det, good = [], True
    for r in rs:
        for p in r["points"]:
            if abs(p["f"] - f) > 1e-9 or abs(p["noise"] - noise) > 1e-9:
                continue
            v = {c: p["decision"][c]["verdict"] for c in ("W1", "Dprime", "Sprime")}
            det.append((p["b"], v))
            good &= all(x == want for x in v.values())
    return ("pass" if good else "fail"), det


def photon_gate(runs, beta, f, noise=0.0):
    """Quantitative photon gate (after the round-3 review): windows EXCLUDED at every b, and the q1 coupling flat in b at the
    Coulomb level. Returns (status, details)."""
    st, det = gate(runs, "u1", beta, f, "EXCLUDED", noise)
    if st == "missing":
        return st, {}
    pts = [p for r in runs if r["group"] == "u1" and abs(r["beta"] - beta) < 1e-9 for p in r["points"]
           if abs(p["f"] - f) < 1e-9 and abs(p["noise"] - noise) < 1e-9]
    b1 = [(p["b"], p["beta"][0], p["beta_err"][0]) for p in pts]
    mean = float(np.mean([x for _, x, _ in b1]))
    flat = all(abs(x - mean) <= PHOTON_FLAT["rel_tol"] * mean + 2 * e for _, x, e in b1)
    level = mean >= PHOTON_FLAT["min_level"] * beta
    ok = st == "pass" and flat and level
    return ("pass" if ok else "fail"), {"windows": det, "q1_by_b": b1, "mean": mean, "flat": flat, "level": level}


def summary(runs):
    out = {}
    print("\n=== controls")
    variants = sorted({(p["f"], p["noise"]) for r in runs if r["group"] == "u1" for p in r["points"]})
    out["photon"] = {}
    out["photon_all"] = {}
    for beta in sorted({r["beta"] for r in runs if r["group"] == "u1" and r["beta"] >= 1.05}):
        for f, nz in variants:
            st, det = photon_gate(runs, beta, f, nz)
            if st == "missing":
                continue
            out["photon_all"][f"beta{beta}_f{f}_noise{nz:g}"] = st
            if abs(beta - GATES["photon_beta"]) < 1e-9 and nz == 0:
                out["photon"][f] = st
            print(f"  photon (U(1) beta={beta}, f={f}, noise={nz:g}): {st.upper()}  q1 by b {[(b, round(x, 4), round(e, 4)) for b, x, e in det['q1_by_b']]}"
                  f" mean {det['mean']:.4f} flat {det['flat']} level {det['level']}; windows {det['windows']}")
    st, det = gate(runs, "z2", GATES["z2_deconfined_beta"], 0.0, "EXCLUDED")
    w1_only = all(v["W1"] == "EXCLUDED" for _, v in det) if det else None
    out["z2_deconfined_W1"] = "pass" if w1_only else ("missing" if w1_only is None else "fail")
    dp_only = all(v["Dprime"] == "EXCLUDED" for _, v in det) if det else None
    out["z2_deconfined_Dprime"] = "pass" if dp_only else ("missing" if dp_only is None else "fail")
    print(f"  Z2 deconfined (beta={GATES['z2_deconfined_beta']}, f=0): W1 {out['z2_deconfined_W1'].upper()}, D' "
          f"{out['z2_deconfined_Dprime'].upper()} (S' reported, gap-only) {det}")
    for grp, beta in (("u1", GATES["u1_confined_beta"]), ("z2", GATES["z2_confined_beta"])):
        rs = [r for r in runs if r["group"] == grp and abs(r["beta"] - beta) < 1e-9]
        for r in rs:
            bmax = max(p["b"] for p in r["points"])
            v = [(p["b"], p["f"], p["decision"]["W1"]["verdict"], p["decision"]["Dprime"]["verdict"]) for p in r["points"]
                 if p["b"] == bmax]
            out[f"positive_{grp}"] = v
            print(f"  positive control {grp} beta={beta} (confined) at b={bmax}: (b, f, W1, D') {v}")
    print("\n=== SU(2): click table. NOT_EXCLUDED = not excluded on the truncated fit (biased towards false positives: omitted terms add "
          "oscillation); only points whose signal check PASSes count")
    su = sorted([r for r in runs if r["group"] == "su2"], key=lambda r: r["beta"])
    out["su2"] = []
    for r in su:
        for p in r["points"]:
            row = {"beta": r["beta"], "N": r["N"], "b": p["b"], "f": p["f"], "noise": p["noise"], "L": p["L_sqrt_sigma"],
                   "beta_FA": p["beta"], "err": p["beta_err"], "signal": p["signal"]["status"], "counts": p["counts"],
                   "fund_resolved": p["fund_resolved"], "Dprime_torus_value": p["decision"]["Dprime_torus"]["value_hi"],
                   **{c: p["decision"][c]["verdict"] for c in ("W1", "Dprime", "Sprime", "BE")},
                   "Dprime_value": p["decision"]["Dprime"]["value_hi"], "Dprime_lambda_star": p["Dprime_lambda_star"],
                   "W1_value": (p["decision"]["W1"]["value_hi"], p["decision"]["W1"]["value_lo"], p["decision"]["W1"]["stat"])}
            out["su2"].append(row)
            if True:  # every blocking is listed; the decision uses the primary one
                L = f"{p['L_sqrt_sigma']:.2f}" if p["L_sqrt_sigma"] else "?"
                print(f"  beta={r['beta']} N={r['N']} L*sqrt(sigma)={L} f={p['f']:.2f} noise={p['noise']:g} signal {row['signal']}"
                      f"{'' if row['fund_resolved'] else ' (fund. unresolved)'}: b_F={fmt(p['beta'][0], p['beta_err'][0], 3)} "
                      f"b_A={fmt(p['beta'][1], p['beta_err'][1], 3)}  W1 {row['W1']} ({p['decision']['W1']['value_hi']:.3g}/"
                      f"{p['decision']['W1']['value_lo']:.3g} +- {p['decision']['W1']['stat']:.2g})  D' {row['Dprime']} ({row['Dprime_value']:.3g}, "
                      f"lambda* {row['Dprime_lambda_star']:.2g})  S' {row['Sprime']}  BE {row['BE']}")
    nmain = {}
    for r in out["su2"]:
        nmain[r["beta"]] = max(nmain.get(r["beta"], 0), r["N"])
    prim = [r for r in out["su2"] if abs(r["f"] - GATES["primary_f"]) < 1e-9 and r["L"] and r["noise"] == 0 and r["N"] == nmain[r["beta"]]]
    for beta in sorted({r["beta"] for r in prim}):
        rows = sorted([r for r in prim if r["beta"] == beta], key=lambda r: r["L"])
        clicks = [r["L"] for r in rows if r["W1"] == "NOT_EXCLUDED" and r["counts"]]
        dclicks = [r["L"] for r in rows if r["Dprime"] == "NOT_EXCLUDED" and r["counts"]]
        out[f"entry_beta{beta}"] = {"first_inside_L": min(clicks) if clicks else None, "crossing_hi": crossing(rows, 0),
                                    "crossing_lo": crossing(rows, 1), "Dprime_first_inside_L": min(dclicks) if dclicks else None,
                                    "Dprime_crossing": crossing([{**r, "W1_value": (r["Dprime_value"],)} for r in rows], 0)}
        print(f"  beta={beta}: first NOT_EXCLUDED (counted) at L*sqrt(sigma) = {min(clicks) if clicks else 'none'}; gamma_hi = 1 crossing at "
              f"{out[f'entry_beta{beta}']['crossing_hi']}, gamma_lo at {out[f'entry_beta{beta}']['crossing_lo']} (log-linear "
              f"interpolation; C's proxy: 3.3 to 3.9); D' first NOT_EXCLUDED (counted) at {out[f'entry_beta{beta}']['Dprime_first_inside_L']}, "
              f"D' = 1 crossing at {out[f'entry_beta{beta}']['Dprime_crossing']}")
    # item 7 of the round-3 review: for L < 1/T_c (T_c ~ 0.69 sqrt(sigma), recalled) a torus one block thick is deconfined, so
    # a D' (or W1) valid uniformly over tori cannot hold there; a NOT_EXCLUDED below L_DECONF flags a false positive of the method
    out["deconfinement_flags"] = [(r["beta"], r["L"], r["f"], r["noise"], c) for r in out["su2"] if r["L"] and r["L"] < L_DECONF
                                  for c in ("W1", "Dprime", "Sprime", "BE") if r[c] == "NOT_EXCLUDED"]
    print(f"  NOT_EXCLUDED below L*sqrt(sigma) = {L_DECONF} (1/T_c; would be a false positive): {out['deconfinement_flags'] or 'none'}")
    out["scaling"] = scaling(prim)
    if out["scaling"]:
        print(f"  scaling beta 2.3 vs 2.4 (interpolated in L): {out['scaling']}")
    out["volume"] = volume_check(out["su2"])
    for v in out["volume"]:
        print(f"  coarse volume (beta={v['beta']}, b={v['b']}, f={v['f']}, noise={v['noise']:g}): N {v['N']} -> coarse sides {v['sides']}: "
              f"b_F {v['bF']}, b_A {v['bA']}, D' {v['Dp']}; agree within 2 sigma: {v['pass']}")
    noisy = sorted({r["noise"] for r in out["su2"] if r["noise"] > 0})
    for nz in noisy:
        rows = sorted([r for r in out["su2"] if r["noise"] == nz and r["L"] and r["N"] == nmain[r["beta"]]], key=lambda r: (r["beta"], r["L"]))
        print(f"  noisy variant beta_n={nz:g}: " + "; ".join(f"beta={r['beta']} L={r['L']:.2f}: W1 {r['W1']}, D' {r['Dprime']}" for r in rows))
    pg = out["photon"].get(GATES["primary_f"])
    print(f"\n=== reading: photon gate (beta {GATES['photon_beta']}) for the primary blocking: {pg}; all photon variants {out['photon_all']}; "
          f"Z2 deconfined W1: {out['z2_deconfined_W1']}, D': {out['z2_deconfined_Dprime']}")
    return out


def volume_check(rows):
    """Same (beta, b, f, noise) at different N: couplings and D' against the coarse torus side."""
    res = []
    keys = {(r["beta"], r["b"], r["f"], r["noise"]) for r in rows}
    for k in sorted(keys):
        rs = sorted([r for r in rows if (r["beta"], r["b"], r["f"], r["noise"]) == k], key=lambda r: r["N"])
        if len(rs) < 2:
            continue
        ok = all(abs(rs[0]["beta_FA"][j] - r["beta_FA"][j]) < 2 * math.hypot(rs[0]["err"][j], r["err"][j]) for r in rs[1:] for j in (0, 1))
        res.append({"beta": k[0], "b": k[1], "f": k[2], "noise": k[3], "N": [r["N"] for r in rs], "sides": [r["N"] // k[1] for r in rs],
                    "bF": [round(r["beta_FA"][0], 5) for r in rs], "bA": [round(r["beta_FA"][1], 5) for r in rs],
                    "Dp": [round(r["Dprime_value"], 4) for r in rs], "pass": ok})
    return res


def crossing(rows, which):
    """L where gamma (hi: which = 0, lo: 1) crosses 1, log-linear interpolation between measured points."""
    pts = [(r["L"], r["W1_value"][which]) for r in rows]
    for (L1, g1), (L2, g2) in zip(pts, pts[1:]):
        if (g1 - 1) * (g2 - 1) <= 0 and g1 > 0 and g2 > 0:
            return round(L1 + (L2 - L1) * math.log(g1) / (math.log(g1) - math.log(g2)), 3)
    if pts and all(g < 1 for _, g in pts):
        return f"< {pts[0][0]:.2f}"
    if pts and all(g > 1 for _, g in pts):
        return f"> {pts[-1][0]:.2f}"
    return None


def scaling(prim):
    a = sorted([r for r in prim if abs(r["beta"] - 2.3) < 1e-9], key=lambda r: r["L"])
    b = [r for r in prim if abs(r["beta"] - 2.4) < 1e-9]
    res = []
    for r in b:
        for r1, r2 in zip(a, a[1:]):
            if r1["L"] <= r["L"] <= r2["L"]:
                w = (r["L"] - r1["L"]) / (r2["L"] - r1["L"])
                for k, name in ((0, "b_F"), (1, "b_A")):
                    v1, v2 = r1["beta_FA"][k], r2["beta_FA"][k]
                    if v1 > 0 and v2 > 0:
                        vi = math.exp((1 - w) * math.log(v1) + w * math.log(v2))
                        ei = math.hypot((1 - w) * r1["err"][k] / v1, w * r2["err"][k] / v2) * vi
                    else:
                        vi = (1 - w) * v1 + w * v2
                        ei = math.hypot((1 - w) * r1["err"][k], w * r2["err"][k])
                    diff = r["beta_FA"][k] - vi
                    ce = math.hypot(r["err"][k], ei)
                    res.append({"L": round(r["L"], 3), "coupling": name, "beta2.4": r["beta_FA"][k], "beta2.3_interp": vi,
                                "diff_sigma": diff / ce if ce > 0 else float("inf"), "pass": abs(diff) < 2 * ce})
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+")
    ap.add_argument("--out")
    ap.add_argument("--gf-grid", type=float, nargs=2, default=None, help="t_min dt of the alpha_GF table (pipeline test only)")
    ap.add_argument("--gate-photon", action="store_true", help="only the photon gate for the primary blocking; prints PHOTON GATE PASSED/FAILED")
    a = ap.parse_args()
    if a.gf_grid:
        GF_GRID[:] = a.gf_grid
    files = sorted({f for p in a.files for f in glob.glob(p)})
    runs = [analyse_run(f) for f in files]
    n = counts()
    for Lt in (INF_L, 4, 3):
        print(f"D' pair table on a {Lt}^4 torus (n_P, n_R, dist): multiplicity { {k: pairs(Lt).count(k) for k in sorted(set(pairs(Lt)))} }")
    print(f"factor counts (enumerated): plaquette meets {n['P']['P']} plaquettes and {n['P']['R']} rectangles; rectangle meets "
          f"{n['R']['P']} plaquettes and {n['R']['R']} rectangles")
    for r in runs:
        print_run(r)
    s = summary(runs)
    if a.gate_photon:
        st = s["photon"].get(GATES["primary_f"], "missing")
        print("PHOTON GATE PASSED" if st == "pass" else f"PHOTON GATE FAILED ({st})")
    if a.out:
        json.dump({"runs": runs, "summary": s, "counts": n}, open(a.out, "w"), indent=1, default=float)
    return 0


if __name__ == "__main__":
    sys.exit(main())
