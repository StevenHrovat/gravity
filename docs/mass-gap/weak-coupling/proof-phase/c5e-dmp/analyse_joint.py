"""Analysis of the joint measurement of z0(L) and z_e(L) (c5e-dmp, PREREG-JOINT.md), written 2026-11-22 before any data was read with it.

ANALYSIS CHOICES (everything the prereg leaves open; the prereg wins wherever it speaks). Written before the first run on data; only the
synthetic --selftest existed then. See the "Fix log" at the end of this docstring for any later change.

Inputs/bookkeeping
 1. Input: .npz of lattice/run_su2_gpu.py (glue (n,8,T), tor (n,4,T), levels 2,6,12,20, chain-major). partial=1 or chains not dividing 20: refused.
 2. Jackknife: 20 contiguous equal bins (analyse.jackknife formula, re-implemented only to keep the replicas for derived quantities; tested
    against analyse.jackknife in --selftest). With 10 chains each bin lies inside one chain.
 3. Scale a*sqrt(sigma) = 0.350, 0.258, 0.1825 (beta 2.3, 2.4, 2.5); the project's torelon values 0.363, 0.273, 0.199 give a second axis column.
Operators and variational step
 4. z0 basis: 8 glueball ops (file order) + 4 flux-pair ops O_pp,k = tor_k(t)^2 = 12 ops (the prereg says 16; 8 + 4 = 12, all 4 levels used). z_e basis: the 4 torelon ops (tor is already the zero-
    momentum sum over lines and the three directions).
 5. Noise drop: with the full data an op is dropped if the jackknife error of its diagonal C(0) is > 0.5*C(0) (C vacuum subtracted as in
    analyse.correlator_matrix). The kept set is fixed from the full data, used unchanged in all replicas. No op left: channel NOT COUNTED.
 6. analyse.best_projection(C, t0=0, t1=1), recomputed in every replica; c(t) = v C(t) v, t = 0..T/2.
 7. m(t) = analyse.cosh_mass(c, t, T) (c(t)/c(t+1), periodic cosh form; the prereg's "c(t-1)/c(t), c(t+1)" is read as this cited function),
    for t = 0..min(T/2-1, 8) (tmax = 8 as analyse_plateau.meff).
 8. Plateau: analyse_plateau.plateau(m, e), imported unchanged; E = m(t*), t* from the full data, replicas at the same t*. COUNTED for z0
    only if t* exists and m(t*+1) is finite with finite error. A NaN in any replica makes that t unusable (no interpolation).
 9. z = L*E (errors scaled by L). Systematic = the same at t*+1, printed next to every number.
z_e counting rule
10. The file holds the torelon summed over the three directions only, so the >= 10 sign flips per chain rule is applied to this sum: per
    measurement the level-0 torelon averaged over the T slices; sign changes counted per chain; counted if the minimum over chains >= 10.
    (Weak at small L: noise near zero also flips the sign. Reported with the flips per chain; no other test.) Diagnostic only, no gate:
    chain mean of that quantity in units of its within-chain rms.
11. z_e also needs a plateau as in 8.
Readings
12. g_gamma(L) = z0g(2L)/z0g(L), z0g(L) = 2L asinh(sin(pi/L)), cross-checked against photon_exact.json at run time.
13. J1 per pair (beta, L, 2L), both z0 counted: g0 = z0(2L)/z0(L), sigma_g = g0 hypot(s1/z1, s2/z2). Rules evaluated at E(t*) (shift 0) and
    E(t*+1) (shift 1), each point with its own t*. DOUBLES needs the DOUBLES condition at both shifts; a shift-0 DOUBLES failing at shift 1
    is NOT RESOLVED; otherwise the verdict is that of shift 0. "Not robust to the plateau choice" if the shift-1 verdict differs from the final one.
14. J2: pair-start "scaling sets" = the J5 sets plus {1.03 (beta 2.4), 1.09 (beta 2.5)} (the two smallest boxes, 6 % apart; the prereg's sets list
    boxes that also occur as doubled partners and have no member there). A set qualifies if DOUBLES pairs start at two different beta in it.
    L_D sqrt(sigma) = smallest start L sqrt(sigma) of a DOUBLES pair in the lowest qualifying set; D-S candidate (zeta0, zeta_e) printed for every
    DOUBLES start in that set (z_e NOT COUNTED if it is). Otherwise "NO START ON THE MEASURED STRETCH".
15. J3: v from step 6 normalised by diag C(0): v_n,i = v_i sqrt(C_ii(0)); w_pp = sum_{O_pp} v_n^2 / sum v_n^2 (kept ops). Delta = E0 - 2E_e at
    shift 0 (shift 1 printed). Needs z0 and z_e counted, else NOT RESOLVED. Switch per beta: g = first (smallest L) GLUEBALL point, f = last
    FLUX-PAIR point with L below g, L_s sqrt(sigma) = midpoint; otherwise "no switch in the measured stretch" with the reason.
16. J4: eta = 1 - g0/2, sigma_eta = sigma_g/2, DOUBLES pairs, by increasing L sqrt(sigma), no verdict.
17. J5: sets of boxes (beta, L): {1.40: (2.3,4), 1.46: (2.5,8)}, {2.06: (2.4,8), 2.10: (2.3,6), 2.19: (2.5,12)}, {2.80: (2.3,8), 2.92: (2.5,16)},
    {4.13: (2.4,16), 4.20: (2.3,12), 4.38: (2.5,24) optional, not in the plan}. Counted members: SCALING OK if every pair agrees within
    2 hypot(s_i, s_j), else ARTEFACTS VISIBLE (spread = max - min); fewer than two counted: NOT RESOLVED.
18. J6: table and plot of z0 and z_e against L sqrt(sigma) with the line z0 = 3.6 L sqrt(sigma); NOT COUNTED points are not plotted.
Controls and outputs
19. Stage 0 control (--control): torelon E_e at beta 2.3, T = 16, L = 6, 8, 10 against results/luscher_summary.json, pass if
    |E_e - E_ref| <= 2 hypot(sigma, sigma_ref) at E(t*) (the earlier numbers used t = a..2a with a plain log mass).
20. Outputs: --out summary JSON, --report text, --plot png. Pilot output carries --label and is never counted.

Usage:
  python analyse_joint.py FILE.npz|GLOB ... [--label TEXT] [--out summary.json] [--report report.txt] [--plot z.png] [--control]
  python analyse_joint.py --selftest

Fix log: (empty at the time of writing)
"""

import argparse
import glob
import json
import os
import sys

import numpy as np

sys.dont_write_bytecode = True  # lattice/ stays untouched
HERE = os.path.dirname(os.path.abspath(__file__))
LATT = os.path.normpath(os.path.join(HERE, "..", "..", "..", "lattice"))
sys.path.insert(0, LATT)
import analyse as A  # noqa: E402
from analyse import best_projection, cosh_mass  # noqa: E402
from analyse_plateau import plateau  # noqa: E402

NBINS = 20
TMAX = 8
A_SQRT_SIGMA = {2.3: 0.350, 2.4: 0.258, 2.5: 0.1825}
A_SQRT_SIGMA_ALT = {2.3: 0.363, 2.4: 0.273, 2.5: 0.199}
SETS_J5 = [  # (name, {box (beta, L): nominal L sqrt(sigma)})
    ("{1.40, 1.46}", {(2.3, 4): 1.40, (2.5, 8): 1.46}),
    ("{2.06, 2.10, 2.19}", {(2.4, 8): 2.06, (2.3, 6): 2.10, (2.5, 12): 2.19}),
    ("{2.80, 2.92}", {(2.3, 8): 2.80, (2.5, 16): 2.92}),
    ("{4.13, 4.20, 4.38}", {(2.4, 16): 4.13, (2.3, 12): 4.20, (2.5, 24): 4.38}),
]
SET_J2_EXTRA = ("{1.03, 1.09}", {(2.4, 4): 1.03, (2.5, 6): 1.09})
DOUBLES_G = 1.8


# ---------------------------------------------------------------- numerics

def corr_matrix(ops):
    """Same as analyse.correlator_matrix (vacuum subtracted, symmetrised), with BLAS products instead of einsum."""
    o = ops - ops.mean(axis=(0, 2), keepdims=True)
    n, k, T = o.shape
    a = o.transpose(1, 0, 2).reshape(k, n * T)
    C = np.zeros((T // 2 + 1, k, k))
    for t in range(T // 2 + 1):
        b = np.roll(o, -t, axis=2).transpose(1, 0, 2).reshape(k, n * T)
        C[t] = a @ b.T / (n * T)
    return 0.5 * (C + np.transpose(C, (0, 2, 1)))


def jack_reps(ops, fn, nbins=NBINS):
    """All replicas of analyse.jackknife (same contiguous bins): returns (full value, reps (nbins, ...))."""
    n = ops.shape[0]
    edges = np.linspace(0, n, nbins + 1).astype(int)
    full = fn(ops)
    reps = []
    for b in range(nbins):
        mask = np.ones(n, bool)
        mask[edges[b]:edges[b + 1]] = False
        reps.append(fn(ops[mask]))
    return full, np.array(reps)


def jack_err(reps):
    nb = len(reps)
    return np.sqrt((nb - 1) / nb * np.sum((reps - reps.mean(axis=0)) ** 2, axis=0))


def analyse_channel(ops, T, pp_mask=None):
    """Variational + cosh effective mass + plateau on one operator basis (steps 4-9).
    ops (n, k, T); pp_mask (k,) bool marks flux-pair operators. Returns dict (with replicas under 'reps') or dict with counted False."""
    k = ops.shape[1]
    d0, reps0 = jack_reps(ops, lambda x: np.diag(corr_matrix(x)[0]))
    e0 = jack_err(reps0)
    keep = (d0 > 0) & (e0 <= 0.5 * d0)
    res = {"n_ops": int(k), "kept": [bool(x) for x in keep]}
    if not keep.any():
        res.update(counted=False, reason="no operator passes the noise rule")
        return res
    o = ops[:, keep]
    M = min(T // 2 - 1, TMAX) + 1

    def fn(x):
        C = corr_matrix(x)
        v = best_projection(C)
        c = np.array([v @ C[t] @ v for t in range(T // 2 + 1)])
        m = np.array([cosh_mass(c, t, T) for t in range(M)])
        vn = v * np.sqrt(np.diag(C[0]))
        return np.concatenate([m, vn ** 2 / np.sum(vn ** 2)])

    full, reps = jack_reps(o, fn)
    err = jack_err(reps)
    m, em = full[:M], err[:M]
    ts = plateau(m, em)
    res.update(m=m.tolist(), em=em.tolist(), t_star=None if ts is None else int(ts), reps=reps, M=M)
    if pp_mask is not None:
        idx = np.where(pp_mask[keep])[0]
        wfull = full[M:][idx].sum() if len(idx) else 0.0
        wreps = reps[:, M:][:, idx].sum(axis=1) if len(idx) else np.zeros(len(reps))
        res["w_pp"] = [float(wfull), float(jack_err(wreps[:, None])[0])]
    if ts is None:
        res.update(counted=False, reason="no plateau")
        return res
    if not (np.isfinite(m[ts + 1]) and np.isfinite(em[ts + 1]) and np.isfinite(em[ts])):
        res.update(counted=False, reason="m(t*+1) or an error is not finite")
        return res
    res["counted"] = True
    return res


def energy(res, L, shift):
    """(E, sigma_E, z, sigma_z) at t* + shift."""
    t = res["t_star"] + shift
    return res["m"][t], res["em"][t], L * res["m"][t], L * res["em"][t]


def flips(tor, chains):
    """Sign changes per chain of the time-averaged level-0 torelon sum (step 10)."""
    s = tor[:, 0, :].mean(axis=1)
    per = len(s) // chains
    out, means = [], []
    for c in range(chains):
        x = s[c * per:(c + 1) * per]
        sg = np.sign(x)
        sg = sg[sg != 0]
        out.append(int(np.sum(sg[1:] != sg[:-1])))
        means.append(float(x.mean() / (x.std() + 1e-300)))
    return out, means


def z0_photon(L):
    return 2 * L * np.arcsinh(np.sin(np.pi / L))


def g_gamma(L):
    return z0_photon(2 * L) / z0_photon(L)


def photon_check():
    p = os.path.join(HERE, "photon_exact.json")
    if not os.path.exists(p):
        return "photon_exact.json not found"
    rows = json.load(open(p))["rows"]
    worst = max(abs(r["z0_one_photon"] - z0_photon(r["L"])) for r in rows)
    return f"photon formula agrees with photon_exact.json (largest difference {worst:.1e})" if worst < 1e-9 else f"MISMATCH {worst:.2e}"


# ---------------------------------------------------------------- one point

def analyse_point(path):
    d = np.load(path)
    if int(d["partial"]):
        raise SystemExit(f"{path}: partial file, refused")
    chains = int(d["chains"])
    if NBINS % chains:
        raise SystemExit(f"{path}: chains = {chains} does not divide {NBINS}")
    beta, L, T = round(float(d["beta"]), 3), int(d["L"]), int(d["T"])
    glue, tor = d["glue"], d["tor"]
    n = glue.shape[0]
    if n % NBINS:
        raise SystemExit(f"{path}: n = {n} not divisible by {NBINS}")
    pp = tor ** 2
    ops0 = np.concatenate([glue, pp], axis=1)
    pp_mask = np.array([False] * glue.shape[1] + [True] * pp.shape[1])
    r0 = analyse_channel(ops0, T, pp_mask)
    re = analyse_channel(tor, T)
    fl, fm = flips(tor, chains)
    asg = A_SQRT_SIGMA.get(round(beta, 1))
    pt = {"file": os.path.basename(path), "beta": beta, "L": L, "T": T, "n_meas": n, "chains": chains,
          "Lsig": None if asg is None else L * asg,
          "Lsig_alt": None if asg is None else L * A_SQRT_SIGMA_ALT[round(beta, 1)],
          "flips_per_chain": fl, "chain_mean_over_rms": fm, "flips_min": min(fl)}
    pt["_r0"], pt["_re"] = r0, re
    pt["z0_counted"] = bool(r0["counted"])
    pt["ze_counted"] = bool(re["counted"] and min(fl) >= 10)
    pt["ze_reason"] = None if pt["ze_counted"] else ("fewer than 10 sign flips in a chain (min %d)" % min(fl) if re["counted"] else re["reason"])
    for key, res, counted in (("z0", r0, pt["z0_counted"]), ("ze", re, pt["ze_counted"])):
        info = {"counted": counted, "t_star": res.get("t_star"), "kept_ops": int(sum(res["kept"])), "of": res["n_ops"],
                "m": res.get("m"), "em": res.get("em")}
        if res["counted"]:  # the energy is shown even if z_e is NOT COUNTED by the flip rule, flagged by "counted"
            for s in (0, 1):
                E, sE, z, sz = energy(res, L, s)
                info[f"E_s{s}"], info[f"sE_s{s}"], info[f"z_s{s}"], info[f"sz_s{s}"] = float(E), float(sE), float(z), float(sz)
        else:
            info["reason"] = res.get("reason")
        pt[key] = info
    if r0["counted"] and "w_pp" in r0:
        pt["z0"]["w_pp"] = r0["w_pp"]
    # J3 quantities
    if pt["z0_counted"] and pt["ze_counted"]:
        pt["J3"] = j3_point(pt)
    else:
        pt["J3"] = {"branch": "NOT RESOLVED", "reason": "z0 or z_e not counted"}
    return pt


def j3_point(pt):
    r0, re = pt["_r0"], pt["_re"]
    out = {}
    for s in (0, 1):
        t0, te = r0["t_star"] + s, re["t_star"] + s
        reps = r0["reps"][:, t0] - 2 * re["reps"][:, te]
        full = r0["m"][t0] - 2 * re["m"][te]
        out[f"Delta_s{s}"] = [float(full), float(jack_err(reps[:, None])[0])]
    E0 = r0["m"][r0["t_star"]]
    D, sD = out["Delta_s0"]
    w = r0["w_pp"][0]
    out["w_pp"] = float(w)
    if not np.isfinite(sD):
        out["branch"] = "NOT RESOLVED"
    elif w >= 0.5 and abs(D) <= 2 * sD + 0.1 * E0:
        out["branch"] = "FLUX-PAIR"
    elif w < 0.5 and D < -2 * sD:
        out["branch"] = "GLUEBALL"
    else:
        out["branch"] = "MIXED"
    return out


# ---------------------------------------------------------------- readings

def single_shift_verdict(g, s, gg):
    if g - 2 * s >= DOUBLES_G:
        return "DOUBLES"
    if g - 2 * s > gg + 0.1 and g + 2 * s < DOUBLES_G:
        return "GROWS, NOT DOUBLING"
    if abs(g - gg) <= 2 * s + 0.1:
        return "FROZEN (photon-like)"
    return "NOT RESOLVED"


def j1_pair(p1, p2):
    L = p1["L"]
    gg = float(g_gamma(L))
    out = {"beta": p1["beta"], "L": L, "L2": p2["L"], "Lsig": p1["Lsig"], "Lsig2": p2["Lsig"], "g_gamma": gg}
    if not (p1["z0_counted"] and p2["z0_counted"]):
        out.update(verdict="NOT RESOLVED", reason="a point does not count")
        return out
    vs = []
    for s in (0, 1):
        z1, s1 = p1["z0"][f"z_s{s}"], p1["z0"][f"sz_s{s}"]
        z2, s2 = p2["z0"][f"z_s{s}"], p2["z0"][f"sz_s{s}"]
        g = z2 / z1
        sg = g * np.hypot(s1 / z1, s2 / z2)
        out[f"g0_s{s}"], out[f"sigma_g_s{s}"], out[f"eta_s{s}"], out[f"sigma_eta_s{s}"] = float(g), float(sg), float(1 - g / 2), float(sg / 2)
        vs.append(single_shift_verdict(g, sg, gg))
    out["verdict_s0"], out["verdict_s1"] = vs
    if vs[0] == "DOUBLES" and vs[1] == "DOUBLES":
        v = "DOUBLES"
    elif vs[0] == "DOUBLES":
        v = "NOT RESOLVED"
    else:
        v = vs[0]
    out["verdict"] = v
    out["not_robust"] = bool(vs[1] != v)
    return out


def build_readings(points):
    box = {(round(p["beta"], 1), p["L"]): p for p in points}
    R = {"photon_check": photon_check()}
    # J1, J4
    pairs = []
    for (b, L), p in sorted(box.items(), key=lambda kv: (kv[0][0], kv[0][1])):
        if (b, 2 * L) in box:
            pairs.append(j1_pair(p, box[(b, 2 * L)]))
    R["J1"] = pairs
    dbl = sorted([q for q in pairs if q["verdict"] == "DOUBLES"], key=lambda q: q["Lsig"])
    R["J4"] = [{"beta": q["beta"], "L": q["L"], "Lsig": q["Lsig"], "eta": q["eta_s0"], "sigma_eta": q["sigma_eta_s0"],
                "eta_s1": q["eta_s1"], "sigma_eta_s1": q["sigma_eta_s1"]} for q in dbl]
    # J2
    sets = [SET_J2_EXTRA] + SETS_J5
    j2 = {"sets": [], "L_D": None}
    found = False
    for name, members in sets:
        starts = [q for q in dbl if (round(q["beta"], 1), q["L"]) in members]
        betas = sorted({q["beta"] for q in starts})
        ok = len(betas) >= 2
        entry = {"set": name, "doubles_starts": [(q["beta"], q["L"], q["Lsig"]) for q in starts], "qualifies": ok}
        if ok and not found:
            found = True
            j2["L_D"] = min(q["Lsig"] for q in starts)
            cand = []
            for q in sorted(starts, key=lambda q: q["Lsig"]):
                p = box[(round(q["beta"], 1), q["L"])]
                c = {"beta": q["beta"], "L": q["L"], "Lsig": q["Lsig"], "zeta0": [p["z0"]["z_s0"], p["z0"]["sz_s0"]]}
                c["zeta_e"] = [p["ze"]["z_s0"], p["ze"]["sz_s0"]] if p["ze_counted"] else "NOT COUNTED"
                cand.append(c)
            j2["candidates"] = cand
            entry["lowest_qualifying"] = True
        j2["sets"].append(entry)
    if not found:
        j2["verdict"] = "NO START ON THE MEASURED STRETCH"
    R["J2"] = j2
    # J3 switch per beta
    sw = {}
    for b in sorted({k[0] for k in box}):
        pts = sorted([p for k, p in box.items() if k[0] == b], key=lambda p: p["L"])
        br = [(p["L"], p["Lsig"], p["J3"]["branch"]) for p in pts]
        g = next((x for x in br if x[2] == "GLUEBALL"), None)
        if g is None:
            sw[str(b)] = {"branches": br, "switch": "no switch in the measured stretch (no GLUEBALL point)"}
            continue
        f = [x for x in br if x[2] == "FLUX-PAIR" and x[0] < g[0]]
        if not f:
            sw[str(b)] = {"branches": br, "switch": "no switch in the measured stretch (no FLUX-PAIR point below the first GLUEBALL point)"}
            continue
        sw[str(b)] = {"branches": br, "switch": 0.5 * (f[-1][1] + g[1]), "between": [f[-1][1], g[1]]}
    R["J3_switch"] = sw
    # J5
    j5 = []
    for name, members in SETS_J5:
        pts = [(nom, box[(b, L)]) for (b, L), nom in members.items() if (b, L) in box and box[(b, L)]["z0_counted"]]
        e = {"set": name, "counted": [(nom, p["beta"], p["L"], p["z0"]["z_s0"], p["z0"]["sz_s0"],
                                       p["Lsig_alt"]) for nom, p in pts]}
        if len(pts) < 2:
            e["verdict"] = "NOT RESOLVED (fewer than two counted members)"
        else:
            ok = all(abs(a["z0"]["z_s0"] - b2["z0"]["z_s0"]) <= 2 * np.hypot(a["z0"]["sz_s0"], b2["z0"]["sz_s0"])
                     for i, (_, a) in enumerate(pts) for (_, b2) in pts[i + 1:])
            zs = [p["z0"]["z_s0"] for _, p in pts]
            e["verdict"] = "SCALING OK" if ok else "ARTEFACTS VISIBLE"
            e["spread"] = float(max(zs) - min(zs))
        j5.append(e)
    R["J5"] = j5
    return R


# ---------------------------------------------------------------- control

def control(points):
    p = os.path.normpath(os.path.join(HERE, "..", "..", "..", "results", "luscher_summary.json"))
    ref = {int(L): (E, s) for L, E, s, _ in json.load(open(p))["points"]}
    out, ok = [], True
    for L in (6, 8, 10):
        pt = next((q for q in points if q["L"] == L and abs(q["beta"] - 2.3) < 1e-6 and q["T"] == 16), None)
        if pt is None or not pt["ze"].get("E_s0"):
            out.append({"L": L, "result": "no counted-by-plateau torelon energy"})
            ok = False
            continue
        E, sE = pt["ze"]["E_s0"], pt["ze"]["sE_s0"]
        Er, sr = ref[L]
        dev = abs(E - Er) / np.hypot(sE, sr)
        out.append({"L": L, "E": E, "sE": sE, "E_ref": Er, "sE_ref": sr, "dev_sigma": float(dev), "t_star": pt["ze"]["t_star"],
                    "E_s1": pt["ze"]["E_s1"], "sE_s1": pt["ze"]["sE_s1"], "pass": bool(dev <= 2)})
        ok = ok and dev <= 2
    return {"points": out, "passed": bool(ok)}


# ---------------------------------------------------------------- output

def clean(x):
    if isinstance(x, dict):
        return {k: clean(v) for k, v in x.items() if not k.startswith("_") and k != "reps"}
    if isinstance(x, (list, tuple)):
        return [clean(v) for v in x]
    if isinstance(x, (np.floating, float)):
        return None if not np.isfinite(x) else float(x)
    if isinstance(x, (np.integer,)):
        return int(x)
    if isinstance(x, (np.bool_,)):
        return bool(x)
    return x


def fmt(v, s, nd=3):
    return f"{v:.{nd}f}({s:.{nd}f})"


def report(points, R, label, ctrl):
    L_ = []
    ap = L_.append
    ap(f"JOINT MEASUREMENT REPORT  [{label}]")
    ap("")
    ap("Per point (E, z = L E at t*, and at t*+1 as systematic):")
    for p in sorted(points, key=lambda p: (p["beta"], p["L"])):
        ls = "?" if p["Lsig"] is None else f"{p['Lsig']:.2f}"
        ap(f"- beta {p['beta']:.2f} L {p['L']:2d} T {p['T']} (L sqrt(sigma) {ls}), n {p['n_meas']} in {p['chains']} chains")
        for key, nm in (("z0", "z0"), ("ze", "z_e")):
            i = p[key]
            if i.get("E_s0") is None:
                ap(f"    {nm}: NOT COUNTED ({i.get('reason')}), kept ops {i['kept_ops']}/{i['of']}")
                continue
            flag = "" if i["counted"] else "  [NOT COUNTED: " + str(p["ze_reason"]) + "; value shown for information]"
            ap(f"    {nm}: t* {i['t_star']}  E {fmt(i['E_s0'], i['sE_s0'])}  z {fmt(i['z_s0'], i['sz_s0'])}   | t*+1: E {fmt(i['E_s1'], i['sE_s1'])}  "
               f"z {fmt(i['z_s1'], i['sz_s1'])}  kept ops {i['kept_ops']}/{i['of']}{flag}")
        ap(f"    z_e sign flips per chain: {p['flips_per_chain']}  (min {p['flips_min']})")
        j = p["J3"]
        if "w_pp" in j:
            ap(f"    J3: w_pp {j['w_pp']:.3f}  Delta = E0 - 2E_e {fmt(*j['Delta_s0'])} (t*+1: {fmt(*j['Delta_s1'])})  -> {j['branch']}")
        else:
            ap(f"    J3: {j['branch']} ({j.get('reason')})")
    ap("")
    ap("J1 doubling per pair  (photon: " + R["photon_check"] + ")")
    for q in R["J1"]:
        if "g0_s0" not in q:
            ap(f"- beta {q['beta']:.2f} {q['L']}->{q['L2']}: NOT RESOLVED ({q['reason']})")
            continue
        ap(f"- beta {q['beta']:.2f} {q['L']}->{q['L2']} (L sqrt(sigma) {q['Lsig']:.2f}->{q['Lsig2']:.2f}): g0 {fmt(q['g0_s0'], q['sigma_g_s0'])} "
           f"[t*+1: {fmt(q['g0_s1'], q['sigma_g_s1'])}], g_gamma {q['g_gamma']:.3f}: {q['verdict']}"
           f"{'  (not robust to the plateau choice)' if q['not_robust'] else ''}   [shift 0: {q['verdict_s0']}, shift 1: {q['verdict_s1']}]")
    ap("")
    j2 = R["J2"]
    ap("J2 start: " + (f"L_D sqrt(sigma) = {j2['L_D']:.2f}" if j2["L_D"] is not None else j2["verdict"]))
    for e in j2["sets"]:
        ap(f"   set {e['set']}: DOUBLES starts {e['doubles_starts']}  qualifies: {e['qualifies']}")
    for c in j2.get("candidates", []):
        ze = c["zeta_e"] if isinstance(c["zeta_e"], str) else fmt(*c["zeta_e"])
        ap(f"   D-S candidate beta {c['beta']:.2f} L {c['L']}: zeta0 {fmt(*c['zeta0'])}, zeta_e {ze}")
    ap("")
    ap("J3 branch and switch per beta:")
    for b, s in R["J3_switch"].items():
        sw = s["switch"] if isinstance(s["switch"], str) else f"L_s sqrt(sigma) = {s['switch']:.2f} (between {s['between'][0]:.2f} and {s['between'][1]:.2f})"
        ap(f"   beta {b}: {[(x[0], x[2]) for x in s['branches']]}  switch: {sw}")
    ap("")
    ap("J4 loss eta = 1 - g0/2 (DOUBLES pairs):")
    for q in R["J4"]:
        ap(f"   beta {q['beta']:.2f} {q['L']}->{2 * q['L']} (L sqrt(sigma) {q['Lsig']:.2f}): eta {fmt(q['eta'], q['sigma_eta'])}  [t*+1 {fmt(q['eta_s1'], q['sigma_eta_s1'])}]")
    ap("")
    ap("J5 scaling:")
    for e in R["J5"]:
        extra = f", spread {e['spread']:.3f}" if "spread" in e else ""
        ap(f"   {e['set']}: {e['verdict']}{extra}; members {[(m[0], m[1], m[2], round(m[3], 3), round(m[4], 3)) for m in e['counted']]}")
    ap("")
    ap("J6: z0 and z_e against L sqrt(sigma) (z0 = 3.6 L sqrt(sigma) for orientation): see the table above and the plot.")
    if ctrl is not None:
        ap("")
        ap("CONTROL (torelon energies at beta 2.3, T = 16, against results/luscher_summary.json, 2 sigma): " + ("PASSED" if ctrl["passed"] else "FAILED"))
        for c in ctrl["points"]:
            if "E" in c:
                ap(f"   L {c['L']}: E {fmt(c['E'], c['sE'], 4)} (t* {c['t_star']}; at t*+1 {fmt(c['E_s1'], c['sE_s1'], 4)}), reference {fmt(c['E_ref'], c['sE_ref'], 4)}, "
                   f"deviation {c['dev_sigma']:.2f} sigma: {'ok' if c['pass'] else 'FAIL'}")
            else:
                ap(f"   L {c['L']}: {c['result']}")
    return "\n".join(L_)


def plot(points, label, path):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig, ax = plt.subplots(figsize=(7, 5))
    cols = {2.3: "tab:blue", 2.4: "tab:green", 2.5: "tab:red"}
    for p in points:
        if p["Lsig"] is None:
            continue
        c = cols.get(round(p["beta"], 1), "k")
        if p["z0_counted"]:
            ax.errorbar(p["Lsig"], p["z0"]["z_s0"], p["z0"]["sz_s0"], fmt="o", color=c)
        if p["ze_counted"]:
            ax.errorbar(p["Lsig"], p["ze"]["z_s0"], p["ze"]["sz_s0"], fmt="s", mfc="none", color=c)
    x = np.linspace(0.5, 5, 50)
    ax.plot(x, 3.6 * x, "k--", lw=0.8, label="z0 = 3.6 L sqrt(sigma)")
    for b, c in cols.items():
        ax.plot([], [], "o", color=c, label=f"beta {b}")
    ax.plot([], [], "ko", label="z0")
    ax.plot([], [], "ks", mfc="none", label="z_e")
    ax.set_xlabel("L sqrt(sigma)")
    ax.set_ylabel("z = L E")
    ax.set_title(label, fontsize=9)
    ax.legend(fontsize=8)
    fig.tight_layout()
    fig.savefig(path, dpi=130)


# ---------------------------------------------------------------- self-test

def selftest():
    rng = np.random.default_rng(1)
    T, n, E = 32, 4000, 0.5
    c = np.cosh(E * (T / 2 - np.arange(T)))
    S = np.fft.fft(c).real
    assert S.min() > 0
    w = rng.standard_normal((n, T))
    x = np.real(np.fft.ifft(np.fft.fft(w, axis=1) * np.sqrt(S), axis=1))
    ops = np.stack([x * a + 0.3 * rng.standard_normal((n, T)) for a in (1.0, 0.7, 1.3)], axis=1)
    # 1. fast correlator = analyse.correlator_matrix
    assert np.allclose(corr_matrix(ops), A.correlator_matrix(ops), rtol=1e-9, atol=1e-12)
    # 2. jackknife replicas = analyse.jackknife
    fn = lambda y: corr_matrix(y)[1].diagonal()
    f1, r = jack_reps(ops, fn)
    f2, e2 = A.jackknife(ops, fn)
    assert np.allclose(f1, f2) and np.allclose(jack_err(r), e2)
    # 3. energy recovery
    res = analyse_channel(ops, T)
    assert res["counted"], res
    Ee, sE, _, _ = energy(res, 1, 0)
    print(f"selftest: t* {res['t_star']}  E {Ee:.4f}({sE:.4f}), true {E}")
    assert abs(Ee - E) <= 3 * sE + 0.01
    # 4. flip counter: 2 chains x 100 measurements, alternating
    tor = np.zeros((200, 1, 4))
    tor[:, 0, :] = np.tile(np.array([1.0, -1.0]), 100)[:, None]
    fl, _ = flips(tor, 2)
    assert fl == [99, 99], fl
    # 5. verdict rules
    assert single_shift_verdict(2.0, 0.1, 1.06) == "DOUBLES"
    assert single_shift_verdict(1.0 + 0.0, 0.05, 1.06) == "FROZEN (photon-like)"
    assert single_shift_verdict(1.5, 0.05, 1.06) == "GROWS, NOT DOUBLING"
    assert single_shift_verdict(1.7, 0.2, 1.06) == "NOT RESOLVED"
    assert abs(g_gamma(4) - 1.1357) < 1e-3 and abs(g_gamma(6) - 1.0638) < 1e-3
    print("selftest: " + photon_check())
    print("selftest OK")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="*")
    ap.add_argument("--label", default="")
    ap.add_argument("--out")
    ap.add_argument("--report")
    ap.add_argument("--plot")
    ap.add_argument("--control", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    paths = []
    for f in a.files:
        paths += sorted(glob.glob(f)) or [f]
    points = [analyse_point(p) for p in paths]
    R = build_readings(points)
    ctrl = control(points) if a.control else None
    txt = report(points, R, a.label or "joint measurement", ctrl)
    print(txt)
    if a.report:
        open(a.report, "w", encoding="utf-8").write(txt + "\n")
    if a.out:
        json.dump(clean({"label": a.label, "points": points, "readings": R, "control": ctrl}), open(a.out, "w"), indent=1)
    if a.plot:
        plot(points, a.label or "joint measurement", a.plot)


if __name__ == "__main__":
    sys.exit(main())
