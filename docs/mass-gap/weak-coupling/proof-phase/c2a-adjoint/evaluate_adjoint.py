"""Evaluate the adjoint half (and the centre half) of the Dobrushin condition D' on Leg C's fitted blocked actions.

Pre-registration: PREREG.md in this folder (written before any SU(2) fit was read). Reads the run files of Leg C
(../../attempts/r3-blocked/runs-gpu/*.npz, format of blocked.py) and reuses Leg C's fit and error code (analyse_blocked.py,
imported read-only). Nothing in Leg C's folder is written.

Usage: python evaluate_adjoint.py RUNS/*.npz [--out SUMMARY.json]

Per point and fit (jackknife):
  centre-blind / centre-charged split of every fitted factor (flip of one link: t -> -t, (1/2)tr V_R -> -(1/2)tr V_R):
    SU(2) plaquette f_e = b_A (4t^2 - 1)/3, f_o = b_F t + b_T (2t^3 - t); rectangle: centre-charged only.
    U(1)  plaquette f_e = q2 cos 2th, f_o = q1 cos th + q3 cos 3th; rectangle centre-charged.   Z2: everything centre-charged.
  a_TV(lam) = sum_pairs tanh(n_P o_e / 2) e^{lam d};  c_TV(lam) = sum_pairs tanh((n_P o_o + n_R o_R)/2) e^{lam d};  H_TV = a + c
  W1 (linearised, Leg C's constants): a_W = 18 (8/3) k_A |b_A|, c_W = 18 (k_F |b_F| + k_T |b_T|) + 90 k_F |b_R|;  H_W = a_W + c_W
  windows b_A*_TV = 1.5 artanh((1 - c_TV)/18), b_A*_W = (1 - c_W)/(48 k_A); Y/X = |b_A| / b_A*
  lam*_H = sup{lam : H_TV(lam) < 1}; consistency: lam*_H <= m L with m/sqrt(sigma) in [3.5, 4.0] (dimension swap)
Verdicts as Leg C: NOT_EXCLUDED if hi + 2 stat < 1, EXCLUDED if lo - 2 stat > 1, else UNDECIDED; a point's verdict needs the base fit
and every extension fit to agree.
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
LEGC = os.path.normpath(os.path.join(HERE, "..", "..", "attempts", "r3-blocked"))
_spec = importlib.util.spec_from_file_location("analyse_blocked", os.path.join(LEGC, "analyse_blocked.py"))
AB = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(AB)

K_F, K_T = AB.K_F, AB.K_T
K_A_C = AB.K_A  # C's bracket (0.0531, 0.0722), reported for comparison
K_A = (2 * math.sqrt(2) / (15 * math.pi), 1 / (5 * math.pi))  # sharpened bracket (kA_bounds.py; amendment before data)
M_OVER_SQRT_SIGMA = (3.5, 3.75, 4.0)
L_DECONF = 1.45
T = np.linspace(-1, 1, 4001)
TH = np.linspace(-np.pi, np.pi, 4001)


def osc(y):
    return float(y.max() - y.min())


def split_osc(group, v):
    """(o_e, o_o, o_R): oscillations of the centre-blind plaquette part, the centre-charged plaquette part, the rectangle."""
    if group == "su2":
        bF, bA, bT, bR = v
        return 4 / 3 * abs(bA), osc(bF * T + bT * (2 * T ** 3 - T)), 2 * abs(bR)
    if group == "u1":
        b1, b2, b3, bR = v
        return 2 * abs(b2), osc(b1 * np.cos(TH) + b3 * np.cos(3 * TH)), 2 * abs(bR)
    bP, bR = v
    return 0.0, 2 * abs(bP), 2 * abs(bR)


def halves_tv(oe, oo, oR, lam=0.0):
    a = sum(math.tanh(nP * oe / 2) * math.exp(lam * d) for nP, nR, d in AB.pairs())
    c = sum(math.tanh((nP * oo + nR * oR) / 2) * math.exp(lam * d) for nP, nR, d in AB.pairs())
    return a, c


def lam_star(oe, oo, oR):
    if sum(halves_tv(oe, oo, oR)) >= 1:
        return 0.0
    lo, hi = 0.0, 1.0
    while sum(halves_tv(oe, oo, oR, hi)) < 1 and hi < 100:
        hi *= 2
    for _ in range(50):
        m = (lo + hi) / 2
        lo, hi = (m, hi) if sum(halves_tv(oe, oo, oR, m)) < 1 else (lo, m)
    return lo


def halves_w(group, v):
    """(a_W_hi, a_W_lo, c_W_hi, c_W_lo), linearised W1 constants as Leg C."""
    if group == "su2":
        bF, bA, bT, bR = (abs(x) for x in v)
        a_hi, a_lo = 18 * 8 / 3 * K_A[1] * bA, 18 * 8 / 3 * K_A[0] * bA
        c_hi = 18 * (K_F * bF + K_T[1] * bT) + 90 * K_F * bR
        c_lo = 18 * (K_F * bF + K_T[0] * bT) + 90 * K_F * bR
        return a_hi, a_lo, c_hi, c_lo
    if group == "u1":  # (U(1) constants as Leg C)
        b1, b2, b3, bR = (abs(x) for x in v)
        a = 18 * (2 / np.pi) * b2
        c = 18 * (2 / np.pi) * (b1 + b3) + 90 * (2 / np.pi) * bR
        return a, a, c, c
    c = 18 * math.tanh(abs(v[0])) + 90 * math.tanh(abs(v[1]))
    return 0.0, 0.0, c, c


def quantities(group, v):
    oe, oo, oR = split_osc(group, v)
    a, c = halves_tv(oe, oo, oR)
    aw_hi, aw_lo, cw_hi, cw_lo = halves_w(group, v)
    r = {"a_TV": a, "c_TV": c, "H_TV": a + c, "lam_H": lam_star(oe, oo, oR),
         "a_W_hi": aw_hi, "a_W_lo": aw_lo, "c_W_hi": cw_hi, "c_W_lo": cw_lo, "H_W_hi": aw_hi + cw_hi, "H_W_lo": aw_lo + cw_lo}
    if group == "su2":
        bA = abs(v[1])
        r["a_W_hi_Cbracket"] = 18 * 8 / 3 * K_A_C[1] * bA
        r["bAstar_TV"] = 1.5 * math.atanh(min(max((1 - c) / 18, 0.0), 0.999999)) if c < 1 else 0.0
        # conservative window: upper constants (smaller window); optimistic: lower constants
        r["bAstar_W_lo"] = max(1 - cw_hi, 0.0) / (18 * 8 / 3 * K_A[1])
        r["bAstar_W_hi"] = max(1 - cw_lo, 0.0) / (18 * 8 / 3 * K_A[0])
        r["YX_TV"] = bA / r["bAstar_TV"] if r["bAstar_TV"] > 0 else float("inf")
        r["YX_W_hi"] = bA / r["bAstar_W_lo"] if r["bAstar_W_lo"] > 0 else float("inf")
        r["YX_W_lo"] = bA / r["bAstar_W_hi"] if r["bAstar_W_hi"] > 0 else float("inf")
    return r


CRITS = {"H_TV": ("H_TV", "H_TV"), "a_TV": ("a_TV", "a_TV"), "c_TV": ("c_TV", "c_TV"),
         "H_W": ("H_W_hi", "H_W_lo"), "a_W": ("a_W_hi", "a_W_lo"), "c_W": ("c_W_hi", "c_W_lo")}


def evaluate_run(path):
    d = np.load(path, allow_pickle=False)
    group = str(d["group"])
    beta = float(d["beta"])
    chains = int(d["chains"])
    N = int(d["N"])
    sched = np.array([tuple(p) + (0.0,) * (4 - len(p)) for p in d["schedule"]])
    asq = AB.a_sqrt_sigma(beta) if group == "su2" else None
    fits = AB.FITS[group]
    cz_b = AB.block_means(d["creutz"], chains) if "creutz" in d.files and d["creutz"].size else None
    data_b = ([AB.block_means(d["hist"].astype(float), chains)] if group == "z2"
              else [AB.block_means(d["M"], chains), AB.block_means(d["c"], chains)])
    out = {"file": os.path.basename(path), "group": group, "beta": beta, "N": N, "n_meas": int(d["n_done"]),
           "partial": int(d["partial"]), "points": []}
    for i, (t, b, f, noise) in enumerate(sched):
        b = int(b)

        def func(*arrs, i=i):
            r = {}
            for name, S in fits.items():
                beta_S = AB.z2_fit(arrs[0][i], S) if group == "z2" else AB.sd_fit(arrs[0][i], arrs[1][i], S)
                v = AB.full_vector(group, S, beta_S)
                for j, x in enumerate(v):
                    r[f"{name}:b{j}"] = float(x)
                for k, x in quantities(group, v).items():
                    r[f"{name}:{k}"] = float(x)
            return r

        full, err = AB.jackknife(data_b, func)
        L = b * asq[0] if asq else None
        pt = {"t": float(t), "b": b, "f": float(f), "noise": float(noise), "L_sqrt_sigma": L, "fits": {}, "verdict": {}}
        for name in fits:
            keys = sorted({k.split(":", 1)[1] for k in full if k.startswith(name + ":")})
            pt["fits"][name] = {k: (full[f"{name}:{k}"], err[f"{name}:{k}"]) for k in keys}
        ext = [n for n in fits if n != "base"]
        for crit, (hi, lo) in CRITS.items():
            vs = []
            for n in ["base"] + ext:
                fv = pt["fits"][n]
                s = max(fv[hi][1], fv[lo][1])
                s = s if np.isfinite(s) else 0.0
                vs.append(AB.decide(fv[hi][0], fv[lo][0], s))
            pt["verdict"][crit] = {"per_fit": dict(zip(["base"] + ext, vs)),
                                   "verdict": vs[0] if all(x == vs[0] for x in vs) else "UNDECIDED",
                                   "value_hi": pt["fits"]["base"][hi][0], "value_lo": pt["fits"]["base"][lo][0],
                                   "stat": pt["fits"]["base"][hi][1]}
        pt["lam_H_min"] = min(pt["fits"][n]["lam_H"][0] for n in fits)
        if group == "su2":
            pt["signal"] = AB.signal_check(cz_b, i, asq)["status"]
            pt["counts"] = pt["signal"] == "PASS"
            pt["mL_band"] = [m * L for m in M_OVER_SQRT_SIGMA]
            pt["gap_consistent"] = pt["lam_H_min"] <= M_OVER_SQRT_SIGMA[2] * L
        else:
            pt["signal"], pt["counts"] = "n/a", True
        out["points"].append(pt)
    return out


def fmt(x, e=None, p=3):
    if x is None or (isinstance(x, float) and not np.isfinite(x)):
        return "inf" if x == float("inf") else "n/a"
    return f"{x:.{p}g}" if e is None or not np.isfinite(e) else f"{x:.{p}g} +- {e:.2g}"


def print_run(r):
    print(f"=== {r['group']} beta={r['beta']} N={r['N']} meas={r['n_meas']}{' (partial)' if r['partial'] else ''}")
    for p in r["points"]:
        b = p["fits"]["base"]
        L = f" L*sqrt(sigma)={p['L_sqrt_sigma']:.2f}" if p["L_sqrt_sigma"] else ""
        nz = f" noise={p['noise']:g}" if p["noise"] else ""
        cpl = ", ".join(fmt(*b[f"b{j}"]) for j in range(len([k for k in b if k.startswith('b') and k[1:].isdigit()])))
        print(f"  b={p['b']:2d} f={p['f']:.2f}{nz}{L} signal {p['signal']}: couplings [{cpl}]")
        v = p["verdict"]
        print(f"      TV: a {fmt(*b['a_TV'])}  c {fmt(*b['c_TV'])}  H {fmt(*b['H_TV'])} -> H {v['H_TV']['verdict']}, a {v['a_TV']['verdict']}, "
              f"c {v['c_TV']['verdict']}; lam*_H {p['lam_H_min']:.3g}")
        print(f"      W1 (linearised): a {fmt(b['a_W_hi'][0])}/{fmt(b['a_W_lo'][0])}  c {fmt(b['c_W_hi'][0])}/{fmt(b['c_W_lo'][0])}  "
              f"H {fmt(b['H_W_hi'][0])}/{fmt(b['H_W_lo'][0])} +- {fmt(b['H_W_hi'][1])} -> H {v['H_W']['verdict']}, a {v['a_W']['verdict']}")
        if r["group"] == "su2":
            print(f"      windows b_A*: TV {fmt(b['bAstar_TV'][0])}, W1 {fmt(b['bAstar_W_lo'][0])} to {fmt(b['bAstar_W_hi'][0])}; "
                  f"Y/X: TV {fmt(*b['YX_TV'])}, W1 {fmt(b['YX_W_lo'][0])} to {fmt(b['YX_W_hi'][0])}; "
                  f"gap consistency lam*_H <= m L ({fmt(p['mL_band'][2])}): {p['gap_consistent']}")


def crossing(rows, key):
    pts = [(r["L"], r[key]) for r in rows if r[key] > 0]
    for (L1, g1), (L2, g2) in zip(pts, pts[1:]):
        if (g1 - 1) * (g2 - 1) <= 0:
            return round(L1 + (L2 - L1) * math.log(g1) / (math.log(g1) - math.log(g2)), 3)
    if pts and all(g < 1 for _, g in pts):
        return f"< {pts[0][0]:.2f}"
    if pts and all(g > 1 for _, g in pts):
        return f"> {pts[-1][0]:.2f}"
    return None


def summary(runs):
    out = {"gates": {}, "su2": [], "entry": {}, "flags": []}
    print("\n=== gates")
    for r in runs:
        if r["group"] == "u1" and r["beta"] >= 1.05:
            for p in r["points"]:
                key = f"photon_beta{r['beta']}_f{p['f']}_noise{p['noise']:g}"
                ok = p["verdict"]["H_TV"]["verdict"] == "EXCLUDED" and p["verdict"]["H_W"]["verdict"] == "EXCLUDED"
                out["gates"].setdefault(key, True)
                out["gates"][key] &= ok
                print(f"  {key} b={p['b']}: H_TV {p['verdict']['H_TV']['verdict']}, H_W {p['verdict']['H_W']['verdict']} "
                      f"(adjoint half alone: TV {p['verdict']['a_TV']['verdict']}, W {p['verdict']['a_W']['verdict']}; centre half TV "
                      f"{fmt(p['fits']['base']['c_TV'][0])})")
        if r["group"] == "z2" and abs(r["beta"] - 0.6) < 1e-9:
            for p in r["points"]:
                ok = p["verdict"]["H_TV"]["verdict"] == "EXCLUDED" and p["verdict"]["H_W"]["verdict"] == "EXCLUDED"
                out["gates"].setdefault("z2_deconfined", True)
                out["gates"]["z2_deconfined"] &= ok
                print(f"  z2 deconfined b={p['b']}: H_TV {p['verdict']['H_TV']['verdict']}, H_W {p['verdict']['H_W']['verdict']}")
        if r["group"] in ("u1", "z2") and r["beta"] in (0.9, 0.3):
            for p in r["points"]:
                print(f"  positive control {r['group']} beta={r['beta']} b={p['b']} f={p['f']}: H_TV {p['verdict']['H_TV']['verdict']}, "
                      f"H_W {p['verdict']['H_W']['verdict']}")
    print("\n=== SU(2) (counted = signal PASS)")
    nmax = {}
    for r in runs:
        if r["group"] == "su2":
            nmax[r["beta"]] = max(nmax.get(r["beta"], 0), r["N"])
    for r in sorted([r for r in runs if r["group"] == "su2"], key=lambda r: (r["beta"], r["N"])):
        for p in r["points"]:
            b = p["fits"]["base"]
            row = {"beta": r["beta"], "N": r["N"], "b": p["b"], "f": p["f"], "noise": p["noise"], "L": p["L_sqrt_sigma"],
                   "signal": p["signal"], "counts": p["counts"], "b_A": b["b1"][0], "b_A_err": b["b1"][1], "b_F": b["b0"][0],
                   "H_TV": b["H_TV"][0], "a_TV": b["a_TV"][0], "c_TV": b["c_TV"][0], "H_W_hi": b["H_W_hi"][0],
                   "H_W_lo": b["H_W_lo"][0], "a_W_hi": b["a_W_hi"][0], "c_W_hi": b["c_W_hi"][0], "YX_TV": b["YX_TV"][0],
                   "YX_W": (b["YX_W_lo"][0], b["YX_W_hi"][0]), "below_W1_ceiling_0.28": abs(b["b1"][0]) + 2 * b["b1"][1] < 0.28, "lam_H": p["lam_H_min"], "gap_consistent": p["gap_consistent"],
                   **{f"v_{c}": p["verdict"][c]["verdict"] for c in CRITS}}
            out["su2"].append(row)
            if row["L"] and row["L"] < L_DECONF and any(row[f"v_{c}"] == "NOT_EXCLUDED" for c in ("H_TV", "H_W")):
                out["flags"].append(("deconfinement false positive", row["beta"], row["L"], row["f"], row["noise"]))
            print(f"  beta={r['beta']} N={r['N']} L={fmt(row['L'])} f={row['f']:.2f} noise={row['noise']:g} {row['signal']}: "
                  f"b_A {fmt(row['b_A'], row['b_A_err'])}  H_TV {fmt(row['H_TV'])} ({row['v_H_TV']}; adj {fmt(row['a_TV'])}, centre "
                  f"{fmt(row['c_TV'])})  H_W {fmt(row['H_W_hi'])}/{fmt(row['H_W_lo'])} ({row['v_H_W']})  Y/X TV {fmt(row['YX_TV'])}, "
                  f"W {fmt(row['YX_W'][0])}-{fmt(row['YX_W'][1])}; |b_A| below nonlinear W1 ceiling 0.28: {row['below_W1_ceiling_0.28']}")
    for beta in sorted(nmax):
        prim = sorted([x for x in out["su2"] if x["beta"] == beta and x["N"] == nmax[beta] and abs(x["f"] - 0.5) < 1e-9
                       and x["noise"] == 0 and x["counts"] and x["L"]], key=lambda x: x["L"])
        e = {"H_TV_crossing": crossing(prim, "H_TV"), "H_W_hi_crossing": crossing(prim, "H_W_hi"),
             "H_W_lo_crossing": crossing(prim, "H_W_lo"),
             "first_NOT_EXCLUDED_TV": min([x["L"] for x in prim if x["v_H_TV"] == "NOT_EXCLUDED"], default=None),
             "first_NOT_EXCLUDED_W": min([x["L"] for x in prim if x["v_H_W"] == "NOT_EXCLUDED"], default=None),
             "counted_points": [round(x["L"], 3) for x in prim]}
        out["entry"][beta] = e
        print(f"  entry beta={beta} (counted primary points {e['counted_points']}): {e}")
    print(f"  flags: {out['flags'] or 'none'}")
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+")
    ap.add_argument("--out")
    a = ap.parse_args()
    files = sorted({f for p in a.files for f in glob.glob(p)})
    runs = [evaluate_run(f) for f in files]
    for r in runs:
        print_run(r)
    s = summary(runs)
    if a.out:
        json.dump({"runs": runs, "summary": s}, open(a.out, "w"), indent=1, default=float)
    return 0


if __name__ == "__main__":
    sys.exit(main())
