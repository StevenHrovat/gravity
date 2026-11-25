"""Analyse boundary.py runs (PREREG-BOUNDARY.md): boundary-influence profiles, decay lengths in lattice and physical units, the flux
witnesses, the photon test and the Ising-gauge (Z2) test, the coupled-chain estimate of k_V(y), and the admissibility fractions.

Usage: python analyse_boundary.py RUNS/*.npz [--out SUMMARY.json]

'run' files are grouped by (group, beta, ell); within a group every BC is compared with 'calm' (a flux or twist BC with a non-default
flux is labelled e.g. 'flux_phi1'). 'couple' files are reported one by one. Errors: blocked standard errors (each chain cut into blocks
so that a run has at least 20 blocks; blocks never cross chains); runs with different BCs are independent, so errors of differences and
ratios add in quadrature. Coupled pairs share their random numbers, so their witness differences are taken pair by pair.

Definitions (fixed in PREREG-BOUNDARY.md; change them there first)
------------------------------------------------------------------
Delta_P(d)    plaquette difference bc - calm at plaquette depth d, flux plane (01) and the other five planes separately.
decay length  weighted fit ln|Delta(d)| = c - d / xi over the TAIL window: d >= max(1, ceil(D_TAIL / (a sqrt(sigma)))) and the
              consecutive points from there whose |Delta| exceeds 3 errors with one sign (at least 2 points). D_TAIL = 0.3 / sqrt(sigma)
              skips the first lattice spacings, where lattice artefacts set the shape. Also: the 'all' window d >= 1 and the step-wise
              xi_eff(d) = 1 / ln(Delta(d) / Delta(d + 1)). Physical: xi * a sqrt(sigma) (units 1 / sqrt(sigma)).
D(R, d2)      flux deficit 1 - W_bc / W_calm of the centred R x R loop in the flux plane at slice depth d2, from the smeared loops when
              the runs have them (else unsmeared). D_deep(R): W averaged over the deep slices d2 >= ceil(ell / 4).
predictions   free field (Coulomb, the flux spreads uniformly): D_C(R) = 1 - cos(PHI R^2 / ell^2);
              confined with random centre vortices (SU(2), Z2 disordered): D_V(R) = 1 - rho_V,
              rho_V = [(e^{-sA} - e^{-s(L2 - A)}) / (1 - e^{-s L2})] / [(e^{-sA} + e^{-s(L2 - A)}) / (1 + e^{-s L2})], s = sigma a^2,
              A = R^2, L2 = ell^2 (a heuristic: independent vortex piercings with the parity fixed by the BC).
F_bar         flux witness (BLUEPRINT-REDUCTION.md 4.1, witness 2), U(1): mean sin theta_p over the flux-plane plaquettes of the inner
              half-box (depth >= ell / 4), bc minus calm, divided by the free-field value sin(PHI / ell^2) <cos theta_p>_calm.
              About 1 in the Coulomb phase at every ell (scale invariant), about 0 when the flux is screened.
k_hat(y)      coupled-chain upper estimate of the boundary influence of shell link y (W variant): mean of sum_e rho(U_e, U'_e) / rho_y
              over the measurements after the first third (coupled-pair equilibration); R_face = n_shell * k_hat(face) / n_dynamic,
              the GDS ratio sum_y k(y) / |V| with every shell link given the face-centre value (an upper-side proxy).
"""

import argparse
import glob
import json
import math
import os
import sys
from collections import defaultdict

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
D_TAIL = 0.3          # tail window starts at this distance in units of 1 / sqrt(sigma)
MIN_BLOCKS = 20
DEFAULT_PHI = {"su2": 1.0, "u1": 2.0, "z2": 1.0}  # in units of pi, as boundary.py
# a sqrt(sigma): ours (results/ttl_summary.json, TTL scan), Teper hep-th/9812187 Table 10 for beta not covered
TEPER = {2.3: (0.3687, 0.0022), 2.4: (0.2686, 0.0021), 2.5: (0.1834, 0.0026), 2.6: (0.1326, 0.0030), 2.7: (0.1005, 0.0020),
         2.85: (0.0636, 0.0012)}
# Photon test (PREREG-BOUNDARY.md, criterion P), U(1) flux against calm, at each ell with both betas; the gate uses gate_ells only
# (beta = 0.9 is close to the transition, its flux screening length is a few lattice units, so small boxes are reported as a trend)
PHOTON = {"beta_coulomb": 1.1, "beta_confined": 0.9, "gate_ells": (12,),
          "coulomb_min": 0.5,        # P1: Coulomb: F_bar ratio >= 0.5 and D_deep(R_ph) >= 0.5 D_C(R_ph)
          "coulomb_no_decay": 0.5,   # P2: Coulomb D(R_ph, d2_max) / D(R_ph, 1) >= 0.5 (no decay into the box)
          "confined_max": 0.2,       # P3: confined F_bar ratio <= 0.2, or within 2 errors of 0 (large loops are unmeasurable there:
                                     #     area law; their deficit is reported at the largest measurable R, not judged)
          "sigma_sep": 3.0}          # P4: Coulomb and confined F_bar ratios differ by more than 3 combined errors


def a_sqrt_sigma(beta):
    p = os.path.join(HERE, "..", "results", "ttl_summary.json")
    try:
        for r in json.load(open(p)):
            if abs(r["beta"] - beta) < 1e-9 and r.get("a_sqrt_sigma"):
                return tuple(r["a_sqrt_sigma"]), "ours (TTL scan)"
    except OSError:
        pass
    t = TEPER.get(round(beta, 3))
    return (t, "Teper Table 10") if t else (None, None)


def blocks(x, chains):
    """x (n_meas, B, ...) -> block means (nblocks, ...), blocks inside chains."""
    n = x.shape[0]
    per = min(max(1, math.ceil(MIN_BLOCKS / chains)), n)
    sz = n // per
    xb = x[:per * sz].reshape((per, sz) + x.shape[1:]).mean(axis=1)
    return xb.reshape((per * x.shape[1],) + x.shape[2:])


def mean_err(x, chains):
    b = blocks(x, chains)
    return b.mean(axis=0), b.std(axis=0, ddof=1) / np.sqrt(b.shape[0])


def exp_fit(d, y, e):
    """Weighted fit ln|y| = c - d / xi; returns xi, err (or None)."""
    if len(d) < 2 or not (np.all(y > 0) or np.all(y < 0)):
        return None, None
    ly = np.log(np.abs(y))
    w = (y / e) ** 2
    A = np.vstack([np.ones(len(d)), d]).T
    cov = np.linalg.inv(A.T @ (w[:, None] * A))
    c = cov @ (A.T @ (w * ly))
    if c[1] >= 0:
        return None, None
    return float(-1 / c[1]), float(np.sqrt(cov[1, 1]) / c[1] ** 2)


def decay(delta, err, d0):
    """Leading run of 3-sigma points of one sign from depth d0 on, then the fit."""
    k = d0
    while k < len(delta) and abs(delta[k]) > 3 * err[k] and np.sign(delta[k]) == np.sign(delta[d0]):
        k += 1
    idx = np.arange(d0, k)
    xi, xe = exp_fit(idx.astype(float), delta[idx], err[idx])
    return xi, xe, idx.tolist()


def rho_vortex(R, ell, s):
    A, L2 = R * R, ell * ell
    num = (np.exp(-s * A) - np.exp(-s * (L2 - A))) / (1 - np.exp(-s * L2))
    den = (np.exp(-s * A) + np.exp(-s * (L2 - A))) / (1 + np.exp(-s * L2))
    return num / den


def label(d):
    bc, g = str(d["bc"]), str(d["group"])
    phi = float(d["phi"]) if "phi" in d else DEFAULT_PHI[g]
    if bc in ("flux", "twist") and abs(phi - DEFAULT_PHI[g]) > 1e-9:
        return f"{bc}_phi{phi:g}"
    return bc


def load(paths):
    runs, couples = defaultdict(dict), []
    for p in paths:
        d = dict(np.load(p, allow_pickle=False))
        d["path"] = p
        if "mode" in d and str(d["mode"]) == "couple":
            couples.append(d)
            continue
        key = (str(d["group"]), round(float(d["beta"]), 4), int(d["ell"]))
        lb = label(d)
        if lb in runs[key]:
            print(f"warning: two runs for {key} {lb}; using {p}")
        runs[key][lb] = d
    return runs, couples


def inner_weights(d, ell):
    pc0 = d["pcount"][0].astype(float)
    inner = np.arange(len(pc0)) >= math.ceil(ell / 4)
    return pc0 * inner / (pc0 * inner).sum()


def profiles(d):
    B = int(d["chains"])
    ell = int(d["ell"])
    pc = d["pcount"].astype(float)
    P, Pe = mean_err(d["plaq"], B)  # (6, nd)
    w = pc[1:]
    other = (d["plaq"][:, :, 1:] * w).sum(axis=2) / np.maximum(w.sum(axis=0), 1)
    O, Oe = mean_err(other, B)
    lk = "loops_s" if "loops_s" in d else "loops"
    ck = "ctrl_s" if "ctrl_s" in d else "ctrl"
    W, We = mean_err(d[lk], B)  # (ell, nd2)
    L, Le = mean_err(d["lines"], B)
    c2 = d["count2"]
    deep = np.arange(len(c2)) >= math.ceil(ell / 4)
    wdeep = (d[lk][..., deep] * c2[deep]).sum(axis=-1) / c2[deep].sum()  # (n, B, ell)
    cdeep = (d[ck][..., deep] * c2[deep]).sum(axis=-1) / c2[deep].sum()
    out = dict(F=(P[0], Pe[0]), O=(O, Oe), W=(W, We), L=(L, Le), Wdeep=mean_err(wdeep, B), Cdeep=mean_err(cdeep, B),
               smeared=lk == "loops_s")
    wi = inner_weights(d, ell)
    out["Pin"] = mean_err((d["plaq"][:, :, 0] * wi).sum(axis=-1), B)
    if "sinp" in d:
        out["S"] = mean_err(d["sinp"], B)
        out["Sin"] = mean_err((d["sinp"] * wi).sum(axis=-1), B)
    return out


def ratio(a, ae, b, be):
    r = a / b
    return r, np.abs(r) * np.sqrt((ae / a) ** 2 + (be / b) ** 2)


def analyse_group(key, bcs):
    group, beta, ell = key
    asq, src = a_sqrt_sigma(beta) if group == "su2" else (None, None)
    res = {"group": group, "beta": beta, "ell": ell, "a_sqrt_sigma": asq, "a_sqrt_sigma_source": src,
           "phys_size": ell * asq[0] if asq else None, "bcs": sorted(bcs)}
    pr = {bc: profiles(d) for bc, d in bcs.items()}
    for bc, d in bcs.items():
        res.setdefault("runs", {})[bc] = {"path": os.path.basename(d["path"]), "n_meas": int(d["plaq"].shape[0]),
                                          "chains": int(d["chains"]), "partial": int(d["partial"]),
                                          "frozen_drift": float(d["frozen_drift"]), "seconds": float(d["seconds"])}
    d_tail = max(1, math.ceil(D_TAIL / asq[0])) if asq else 1
    res["tail_start"] = d_tail
    Rs = np.arange(1, ell + 1)
    res["R_ph"] = ell // 2
    if "calm" in pr:
        c = pr["calm"]
        for bc, p in pr.items():
            if bc == "calm":
                continue
            d = bcs[bc]
            phi = np.pi * (float(d["phi"]) if "phi" in d else DEFAULT_PHI[group])
            r = {}
            for name in ("F", "O"):
                dl = p[name][0] - c[name][0]
                de = np.hypot(p[name][1], c[name][1])
                xi_t, xe_t, it = decay(dl, de, d_tail) if d_tail < len(dl) else (None, None, [])
                xi_a, xe_a, ia = decay(dl, de, 1) if len(dl) > 1 else (None, None, [])
                eff = [float(1 / np.log(dl[k] / dl[k + 1])) if dl[k] * dl[k + 1] > 0 and abs(dl[k]) > abs(dl[k + 1]) else None
                       for k in range(len(dl) - 1)]
                r[name] = {"delta": dl.tolist(), "err": de.tolist(), "xi_tail": xi_t, "xi_tail_err": xe_t, "tail_points": it,
                           "xi_all": xi_a, "xi_all_err": xe_a, "all_points": ia, "xi_eff": eff,
                           "xi_tail_phys": xi_t * asq[0] if (xi_t and asq) else None,
                           "xi_tail_phys_err": math.hypot(xe_t * asq[0], xi_t * asq[1]) if (xi_t and asq) else None}
            rho, rhoe = ratio(p["W"][0], p["W"][1], c["W"][0], c["W"][1])
            rd, rde = ratio(p["Wdeep"][0], p["Wdeep"][1], c["Wdeep"][0], c["Wdeep"][1])
            cd, cde = ratio(p["Cdeep"][0], p["Cdeep"][1], c["Cdeep"][0], c["Cdeep"][1])
            fl = bc.startswith(("flux", "twist"))
            r["deficit"] = {"smeared": bool(p["smeared"]), "phi": phi, "D": (1 - rho).tolist(), "err": rhoe.tolist(),
                            "D_deep": (1 - rd).tolist(), "D_deep_err": rde.tolist(),
                            "ctrl_D_deep": (1 - cd).tolist(), "ctrl_D_deep_err": cde.tolist(),
                            "W_calm_deep": c["Wdeep"][0].tolist(), "W_calm_deep_err": c["Wdeep"][1].tolist(),
                            "D_coulomb": (1 - np.cos(phi * Rs ** 2 / ell ** 2)).tolist() if fl else None}
            if group == "su2" and asq and fl:
                r["deficit"]["D_vortex"] = (1 - rho_vortex(Rs.astype(float), ell, asq[0] ** 2)).tolist()
            dl = p["L"][0] - c["L"][0]
            r["lines"] = {"delta": dl.tolist(), "err": np.hypot(p["L"][1], c["L"][1]).tolist()}
            if "S" in p and group == "u1":  # Z2 angles are 0, pi: the odd witness vanishes identically
                fb = p["Sin"][0] - c["Sin"][0]
                fe = math.hypot(p["Sin"][1], c["Sin"][1])
                free = math.sin(phi / ell ** 2) * c["Pin"][0]
                r["flux_witness"] = {"F_bar": float(fb), "F_bar_err": float(fe), "free_field": float(free),
                                     "ratio": float(fb / free) if fl else None, "ratio_err": float(fe / abs(free)) if fl else None,
                                     "sin_by_depth": p["S"][0].tolist(), "sin_by_depth_err": p["S"][1].tolist()}
            res.setdefault("vs_calm", {})[bc] = r
    if "typical" in bcs:
        d = bcs["typical"]
        B = int(d["chains"])
        w = d["pcount"][1:].astype(float)
        o = (d["plaq"][:, :, 1:, :] * w).sum(axis=2) / np.maximum(w.sum(axis=0), 1)  # (n, B, nd)
        cm = o.mean(axis=0)
        within = np.array([mean_err(o[:, b:b + 1], 1)[1] ** 2 for b in range(B)]).mean(axis=0)
        between = cm.var(axis=0, ddof=1) if B > 1 else np.full(cm.shape[1], np.nan)
        res["typical_spread"] = {"sigma_b": np.sqrt(np.maximum(between - within, 0)).tolist(),
                                 "between_var": between.tolist(), "within_var": within.tolist(), "chains": B}
        if d["periodic_adm"].size:
            m, e = mean_err(d["periodic_adm"], B)
            pp, ppe = mean_err(d["periodic_plaq"], B)
            res["admissibility_periodic"] = {"eps": d["eps"].tolist(), "fraction": m.tolist(), "err": e.tolist(),
                                             "plaq": float(pp), "plaq_err": float(ppe), "n": int(d["periodic_adm"].shape[0])}
    adm = {}
    for bc, d in bcs.items():
        tot = d["pcount"].sum(axis=0)
        m, e = mean_err(d["adm"][:, :, :, -1] / tot[-1], int(d["chains"]))
        adm[bc] = {"fraction_deepest": m.tolist(), "err": e.tolist()}
    res["admissibility_box_deepest"] = adm
    return res


def analyse_couple(d):
    P = int(d["pairs"])
    n = d["k_hat"].shape[0]
    keep = slice(n // 3, n)
    k, ke = mean_err(d["k_hat"][keep], P)
    kr, kre = mean_err(d["k_raw"][keep], P)
    nd, nsh = int(d["n_dynamic"]), int(d["n_shell"])
    dd, dde = mean_err(d["dist_depth"][keep], P)
    dr, dre = mean_err(d["dist_ry"][keep], P)
    # witnesses (lower bounds on k): paired differences of observables between the two chains of each pair, / rho_y
    th = float(d["theta"])
    wit = {}
    for name in ("plaq", "lines", "loops"):
        x = d[name][keep]
        diff = (x[:, 1::2] - x[:, 0::2]) / th
        m, e = mean_err(diff, P)
        wit[name] = {"max_abs": float(np.max(np.abs(m))), "max_abs_sig": float(np.max(np.abs(m) / np.maximum(e, 1e-300)))}
    tseries = d["k_hat"].mean(axis=1)
    thirds = [float(np.mean(t)) for t in np.array_split(tseries, 3)]
    return {"group": str(d["group"]), "beta": float(d["beta"]), "ell": int(d["ell"]), "bc": str(d["bc"]), "y": str(d["y_kind"]),
            "theta": th, "pairs": P, "n_meas": n, "n_dynamic": nd, "n_shell": nsh, "k_hat": float(k), "k_hat_err": float(ke),
            "k_unaligned": float(kr), "k_unaligned_err": float(kre), "R_face": float(nsh * k / nd), "R_face_err": float(nsh * ke / nd),
            "k_thirds": thirds, "dist_by_depth": dd.tolist(), "dist_by_ry": dr.tolist(), "witness": wit,
            "align_iter_mean": float(d["align_iter"].mean()), "path": os.path.basename(d["path"])}


def photon_test(results):
    """Criterion P (PREREG-BOUNDARY.md) for every ell with U(1) flux (PHI = 2 pi) and calm runs at both betas."""
    out = []
    by_ell = defaultdict(dict)
    for r in results:
        if r["group"] == "u1" and "flux" in r.get("vs_calm", {}):
            by_ell[r["ell"]][r["beta"]] = r
    for ell, rs in sorted(by_ell.items()):
        bc_, bf_ = PHOTON["beta_coulomb"], PHOTON["beta_confined"]
        if bc_ not in rs or bf_ not in rs:
            continue
        R = rs[bc_]["R_ph"]
        k = R - 1
        fc, ff = rs[bc_]["vs_calm"]["flux"], rs[bf_]["vs_calm"]["flux"]
        DC = fc["deficit"]["D_coulomb"][k]
        Dc, Dce = fc["deficit"]["D_deep"][k], fc["deficit"]["D_deep_err"][k]
        Df, Dfe = ff["deficit"]["D_deep"][k], ff["deficit"]["D_deep_err"][k]
        prof = fc["deficit"]["D"][k]
        no_decay = prof[-1] / prof[1] if abs(prof[1]) > 0 else float("nan")
        # the odd witness from the Phi = pi/2 runs when present (PROOF-NOTE C9), else from Phi = 2 pi
        wc = rs[bc_]["vs_calm"].get("flux_phi0.5", fc)["flux_witness"]
        wf = rs[bf_]["vs_calm"].get("flux_phi0.5", ff)["flux_witness"]
        Fc, Fce = wc["ratio"], wc["ratio_err"]
        Ff, Ffe = wf["ratio"], wf["ratio_err"]
        p1 = Dc >= PHOTON["coulomb_min"] * DC and Fc >= PHOTON["coulomb_min"]
        p2 = no_decay >= PHOTON["coulomb_no_decay"]
        p3 = (abs(Ff) <= PHOTON["confined_max"]) or (abs(Ff) <= 2 * Ffe)
        p4 = abs(Fc - Ff) > PHOTON["sigma_sep"] * math.hypot(Fce, Ffe)
        # confined loops: reported at the largest R whose calm loop is measurable (W > 5 errors), not judged (area law)
        Wc, We = np.array(ff["deficit"]["W_calm_deep"]), np.array(ff["deficit"]["W_calm_deep_err"])
        okR = np.nonzero((Wc > 5 * We)[:-1])[0]  # R = ell is the frozen boundary loop
        Rm = int(okR.max()) + 1 if okR.size else None
        conf_loop = {"R": Rm, "D_confined": ff["deficit"]["D_deep"][Rm - 1], "err": ff["deficit"]["D_deep_err"][Rm - 1],
                     "D_coulomb_run": fc["deficit"]["D_deep"][Rm - 1], "D_free": fc["deficit"]["D_coulomb"][Rm - 1]} if Rm else None
        out.append({"ell": ell, "R_ph": R, "D_coulomb_free": DC, "D_deep_coulomb": [Dc, Dce], "D_deep_confined": [Df, Dfe],
                    "F_ratio_coulomb": [Fc, Fce], "F_ratio_confined": [Ff, Ffe], "confined_loop_at_measurable_R": conf_loop,
                    "coulomb_profile_ratio_last_over_first": no_decay, "P1": bool(p1), "P2": bool(p2), "P3": bool(p3),
                    "P4": bool(p4), "pass": bool(p1 and p2 and p3 and p4)})
    return out


def fmt(x, e=None, p=3):
    if x is None:
        return "n/a"
    return f"{x:.{p}f}" + (f" +- {e:.{p}f}" if e is not None else "")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="+")
    ap.add_argument("--out")
    ap.add_argument("--photon-gate", action="store_true", help="exit 2 unless at least one photon test ran and all passed")
    a = ap.parse_args()
    paths = [q for p in a.paths for q in glob.glob(p)]
    runs, couples = load(paths)
    results = [analyse_group(k, runs[k]) for k in sorted(runs)]
    for r in results:
        print(f"\n=== {r['group']} beta={r['beta']} ell={r['ell']}  a*sqrt(sigma)={r['a_sqrt_sigma']} "
              f"size*sqrt(sigma)={fmt(r['phys_size'], p=2)}  BCs {r['bcs']}  tail from d={r['tail_start']}")
        for bc, v in r.get("vs_calm", {}).items():
            for name, lab in (("F", "flux plane"), ("O", "other planes")):
                q = v[name]
                print(f"  {bc:10s} Delta_P {lab:12s} by depth: " + " ".join(f"{x:+.1e}({e:.0e})" for x, e in zip(q["delta"], q["err"])))
                print(f"             xi_tail = {fmt(q['xi_tail'], q['xi_tail_err'], 2)} (points {q['tail_points']}), phys "
                      f"{fmt(q['xi_tail_phys'], q['xi_tail_phys_err'], 3)}; xi_all = {fmt(q['xi_all'], q['xi_all_err'], 2)}")
            df = v["deficit"]
            R = r["R_ph"]
            print(f"  {bc:10s} flux deficit D_deep(R) ({'smeared' if df['smeared'] else 'unsmeared'}) R=1..{r['ell']}: "
                  + " ".join(f"{x:+.3f}({e:.3f})" for x, e in zip(df["D_deep"], df["D_deep_err"])))
            if df.get("D_coulomb"):
                print("             free field D_C(R):  " + " ".join(f"{x:.3f}" for x in df["D_coulomb"]))
            if df.get("D_vortex"):
                print("             vortex     D_V(R):  " + " ".join(f"{x:.3f}" for x in df["D_vortex"]))
            print(f"             D(R_ph={R}, d2) profile: " + " ".join(f"{x:+.3f}({e:.3f})" for x, e in zip(df["D"][R - 1], df["err"][R - 1])))
            print("             control plane D_deep(R): " + " ".join(f"{x:+.3f}" for x in df["ctrl_D_deep"]))
            if "flux_witness" in v:
                w = v["flux_witness"]
                print(f"             flux witness F_bar = {w['F_bar']:+.5f} +- {w['F_bar_err']:.5f}, free field {w['free_field']:+.5f}, "
                      f"ratio {fmt(w['ratio'], w['ratio_err'])}")
        if "typical_spread" in r:
            print("  typical-vs-typical sigma_b(d): " + " ".join(f"{x:.1e}" for x in r["typical_spread"]["sigma_b"]))
        if "admissibility_periodic" in r:
            q = r["admissibility_periodic"]
            print("  admissibility (periodic): " + ", ".join(f"eps={e}: {m:.2e} +- {s:.1e}" for e, m, s in zip(q["eps"], q["fraction"], q["err"])))
        for bc, q in r["admissibility_box_deepest"].items():
            print(f"  admissibility (box centre, {bc}): " + ", ".join(f"{m:.2e}" for m in q["fraction_deepest"]))
    pt = photon_test(results)
    for p in pt:
        cl = p["confined_loop_at_measurable_R"]
        cls = (f"confined loop at R={cl['R']}: D {cl['D_confined']:+.3f} +- {cl['err']:.3f} (Coulomb run {cl['D_coulomb_run']:+.3f}, "
               f"free {cl['D_free']:.3f})") if cl else "confined loops unmeasurable"
        print(f"\nPHOTON TEST ell={p['ell']} R_ph={p['R_ph']}: loop deficit Coulomb {fmt(*p['D_deep_coulomb'])} (free {p['D_coulomb_free']:.3f}), "
              f"{cls}; flux witness ratio Coulomb {fmt(*p['F_ratio_coulomb'])}, confined "
              f"{fmt(*p['F_ratio_confined'])}; Coulomb profile last/first {p['coulomb_profile_ratio_last_over_first']:.2f}; "
              f"P1 {p['P1']} P2 {p['P2']} P3 {p['P3']} P4 {p['P4']} -> {'PASS' if p['pass'] else 'FAIL'}")
    cps = [analyse_couple(d) for d in sorted(couples, key=lambda d: (str(d["group"]), float(d["beta"]), int(d["ell"])))]
    if cps:
        print("\nCOUPLED CHAINS (upper estimates of k_V(y); R_face = n_shell k_hat / n_dynamic)")
    for c in cps:
        print(f"  {c['group']:3s} beta={c['beta']:.2f} ell={c['ell']:2d} bc={c['bc']:7s} y={c['y']:6s} k_hat = {c['k_hat']:.2f} +- "
              f"{c['k_hat_err']:.2f} (unaligned {c['k_unaligned']:.1f}; thirds {', '.join(f'{x:.1f}' for x in c['k_thirds'])}) "
              f"R_face = {c['R_face']:.3f} +- {c['R_face_err']:.3f}; witness max |d plaq|/theta {c['witness']['plaq']['max_abs']:.3f} "
              f"({c['witness']['plaq']['max_abs_sig']:.1f} sigma)")
    out = a.out or os.path.join(os.path.dirname(os.path.abspath(paths[0])), "boundary_summary.json")
    with open(out, "w") as f:
        json.dump({"groups": results, "photon_test": pt, "coupled": cps}, f, indent=1,
                  default=lambda x: x.item() if hasattr(x, "item") else str(x))
    print(f"\nwritten {out}")
    gate = [p for p in pt if p["ell"] in PHOTON["gate_ells"]]
    if a.photon_gate and not (gate and all(p["pass"] for p in gate)):
        print("PHOTON GATE: not passed")
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
