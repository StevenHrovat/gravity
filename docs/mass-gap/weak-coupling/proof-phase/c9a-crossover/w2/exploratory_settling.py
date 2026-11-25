"""EXPLORATORY / POST-HOC settling test (EXPLORATORY-SETTLING.md). CPU only; reads the narrow-run launches.

Usage: py exploratory_settling.py runs/narrow/launch_*.json [--out runs/narrow/exploratory_settling.json]
"""
import argparse
import json
import math

import numpy as np

BAD = {"A2", "A3", "A4", "A6"}
CLEAN = {"sampled", "A1"}


def tau_int(x, c=6.0):
    """Integrated autocorrelation time (in measurements) with the self-consistent window W >= c tau (gauge.py convention)."""
    x = np.asarray(x, float) - np.mean(x)
    n = len(x)
    if n < 4 or np.var(x) == 0:
        return float("nan")
    f = np.fft.rfft(x, 2 * n)
    acf = np.fft.irfft(f * np.conj(f))[:n]
    acf /= acf[0]
    tau = 0.5
    for w in range(1, n):
        tau += acf[w]
        if w >= c * tau:
            break
    return max(tau, 0.5)


def spread_time(d, every):
    plateau = d[-3:].mean()
    hit = np.nonzero(d >= (1 - 1 / math.e) * plateau)[0]
    return float((hit[0] + 1) * every) if hit.size else float("nan")


def jk_ratio(bad, clean):
    """Ratio of means and its leave-one-out (over boxes) jackknife error."""
    bad, clean = np.asarray(bad), np.asarray(clean)
    rho = bad.mean() / clean.mean()
    units = [("b", i) for i in range(len(bad))] + [("c", i) for i in range(len(clean))]
    vals = []
    for kind, i in units:
        b = np.delete(bad, i) if kind == "b" else bad
        c = np.delete(clean, i) if kind == "c" else clean
        vals.append(b.mean() / c.mean())
    vals = np.array(vals)
    n = len(vals)
    se = math.sqrt((n - 1) / n * np.sum((vals - vals.mean()) ** 2))
    return float(rho), float(se)


def verdict(rho, se):
    if rho >= 1.5 and rho - 1 > 2 * se:
        return "slower"
    if rho < 1.2 or rho - 1 < 2 * se:
        return "not slower"
    return "inconclusive"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("launches", nargs="+")
    ap.add_argument("--out", default="runs/narrow/exploratory_settling.json")
    a = ap.parse_args()
    boxes = []
    for js in a.launches:
        J = json.load(open(js))
        z = np.load(J["npz"])
        d, w = z["d"].astype(float), z["w"].astype(float)          # (nmeas, P)
        every = J["every"]
        nmeas = d.shape[0]
        half = nmeas // 2
        snaps = z["snap_mid"]
        pairs = z["snap_pairs"]
        for m in J["instances"]:
            f = m["first_pair"]
            sl = range(f, f + 40)                                    # start 0
            taus = [tau_int(w[half:, p]) * every for p in sl]
            ts = [spread_time(d[:, p], every) for p in sl]
            # roughness: fine plaquettes with 1 - tr/2 > 1 in the box, mean over this box's mid snapshots (computed on the CPU)
            boxes.append(dict(beta=J["beta"], yclass=m["yclass"], pool=m["pool"], launch=js, job=m["job"],
                              tau_pairs=taus, t_e_pairs=ts, tau=float(np.nanmean(taus)), t_e=float(np.nanmean(ts)),
                              snap_idx=[int(k) for k, p in enumerate(pairs) if f <= p < f + 80]))
    # roughness of sampled boxes from the snapshots
    try:
        import constrained as C
        geo = C.Geometry(6)
        for b in boxes:
            if b["yclass"] != "sampled":
                continue
            J = json.load(open(b["launch"]))
            z = np.load(J["npz"])
            confs, _ = C.load_confs(f"runs/conf_b{J['beta']}.npz")
            m = [mm for mm in J["instances"] if mm["job"] == b["job"]][0]
            Uf0 = C.frame_links(confs[m["conf"]], geo, tuple(m["shift"]))
            cnt = []
            for k in b["snap_idx"]:
                Uf = Uf0.copy()
                Uf[geo.dyn_lids] = z["snap_mid"][k].astype(np.float64)
                pl = Uf[geo.plaq[:, 0]] * 0
                q = Uf[geo.plaq[:, 0]]
                for j in range(1, 4):
                    g = Uf[geo.plaq[:, j]]
                    g = np.where(geo.plaqd[:, j, None].astype(bool), g * C.CONJ, g)
                    q = C.be_qmul_np(q, g)
                cnt.append(int(np.sum(1 - q[:, 0] > 1.0)))
            b["rough_count"] = float(np.mean(cnt))
    except Exception as e:                                           # report, do not hide
        print("roughness step failed:", e)
    # adaptation of the fine field to fixed defects (A3, A4) at T/2: alignment <Y_l, Phi_l>/|Phi_l| on defect links vs the rest
    try:
        import constrained as C
        geo = C.Geometry(6)
        geo.to_device(np)
        be = C.Backend(False, 1)
        c0 = geo.off + geo.ell // 2
        c0 -= c0 % 2
        a3_sel = [i for i, (y, mu) in enumerate(geo.cl_site) if mu == 1 and y[0] == c0 and y[2] >= c0]
        _, a4_i = C.a4_Y(geo, np.zeros((geo.ncl + 1, 4)))
        for b in boxes:
            if b["yclass"] not in ("A3", "A4"):
                continue
            J = json.load(open(b["launch"]))
            z = np.load(J["npz"])
            confs, _ = C.load_confs(f"runs/conf_b{J['beta']}.npz")
            m = [mm for mm in J["instances"] if mm["job"] == b["job"]][0]
            Uf0 = C.frame_links(confs[m["conf"]], geo, tuple(m["shift"]))
            Y = z["Y_inst"][b["job"]].astype(np.float64)
            sel = a3_sel if b["yclass"] == "A3" else [a4_i]
            rest = [i for i in range(geo.ncl) if i not in set(sel)]
            al_d, al_r = [], []
            for k in b["snap_idx"]:
                Uf = Uf0.copy()
                Uf[geo.dyn_lids] = z["snap_mid"][k].astype(np.float64)
                S = C.PairSampler(be, geo, 0.0, 16.0, Uf[None, None], Y[None, None])
                ph = S.phi(np.arange(geo.ncl))[0, 0]
                al = np.sum(ph * Y[:geo.ncl], axis=-1) / np.maximum(np.linalg.norm(ph, axis=-1), 1e-12)
                al_d.append(float(al[sel].mean()))
                al_r.append(float(al[rest].mean()))
            b["align_defect_T2"] = float(np.mean(al_d))
            b["align_rest_T2"] = float(np.mean(al_r))
    except Exception as e:
        print("alignment step failed:", e)
    out = dict(boxes=boxes, results={})
    for beta in sorted({b["beta"] for b in boxes}):
        B = [b for b in boxes if b["beta"] == beta]
        res = {}
        for meas in ("tau", "t_e"):
            bad = [b[meas] for b in B if b["yclass"] in BAD]
            cln = [b[meas] for b in B if b["yclass"] in CLEAN]
            rho, se = jk_ratio(bad, cln)
            # secondary error: jackknife over pair index across all boxes
            npair = 40
            vals = []
            for i in range(npair):
                bb = [np.nanmean(np.delete(b[meas + "_pairs"], i)) for b in B if b["yclass"] in BAD]
                cc = [np.nanmean(np.delete(b[meas + "_pairs"], i)) for b in B if b["yclass"] in CLEAN]
                vals.append(np.mean(bb) / np.mean(cc))
            vals = np.array(vals)
            se_p = math.sqrt((npair - 1) / npair * np.sum((vals - vals.mean()) ** 2))
            unresolved = meas == "t_e" and np.mean([np.mean(np.array(b["t_e_pairs"]) <= 10) for b in B]) > 0.8
            res[meas] = dict(ratio=rho, se_boxes=se, se_pairs=float(se_p), n_bad=len(bad), n_clean=len(cln),
                             mean_bad=float(np.mean(bad)), mean_clean=float(np.mean(cln)),
                             verdict="unresolved" if unresolved else verdict(rho, se))
        samp = [b for b in B if b["yclass"] == "sampled" and "rough_count" in b]
        if len(samp) >= 4:
            med = np.median([b["rough_count"] for b in samp])
            rough = [b["tau"] for b in samp if b["rough_count"] > med]
            smooth = [b["tau"] for b in samp if b["rough_count"] <= med]
            if rough and smooth:
                rho, se = jk_ratio(rough, smooth)
                res["secondary_rough_vs_smooth_tau"] = dict(ratio=rho, se_boxes=se, n_rough=len(rough),
                                                            n_smooth=len(smooth), verdict=verdict(rho, se))
        out["results"][str(beta)] = res
        print(f"beta {beta}:", json.dumps(res))
    json.dump(out, open(a.out, "w"), indent=1)


if __name__ == "__main__":
    main()
