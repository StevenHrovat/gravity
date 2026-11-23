"""Analysis of the narrow W2 run (W2-PREREG.md section 3 and 5, amendment A6). CPU only.

Per launch (runs/narrow/launch_*.json + .npz):
* k_low(pair) = max over the box plaquettes of |<P>_A - <P>_B| / 2 (time-averaged fundamental plaquette, oscillation bound 2):
  the observable-level lower estimate of the influence of the perturbed link (shell link z, or block variable Y_l).
* noise floor: the same statistic between chain A of start 0 and chain A of start 1 of the same instance and the same
  perturbation (two independent samples of the same law, no perturbation between them): null(pair).
* R_low(instance) = (n_shell / 32) * sum_{32 sampled shell links} k_low / |B|, per start; also with the noise floor subtracted,
  R_low_sub = (n_shell / 32) * sum (k_low - null)_+ / |B|. Statistical error: jackknife over the 32 shell links.
  R_low_diff: the unclipped sum of (k_low - null), unbiased by the clipping, with its jackknife error (the cleaner test).
* k_Y: the same for the 8 block-variable pairs (quasi-locality of the projection), reported, no verdict.
* disagreement plateau (last 3 measurements) per instance.
Verdicts (amendment A6): WL-S FAILS if R_low_sub >= 1 at 2 sigma on sampled instances; otherwise UNRESOLVED (no pass verdict
possible). WL-Q REFUTED for this blocking if some adversarial instance has R_low_sub >= 1 at 2 sigma.
Not available from the saved data: the conditional-mass profile m (per-link disagreement maps were not saved) and the
adversarial column sums C_low over box translates (one box per instance in the narrow design); R_low stands in for C_low.

Usage: py analyse_w2.py runs/narrow/launch_*.json [--out runs/narrow/analysis.json]
"""
import argparse
import json
import math

import numpy as np


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("launches", nargs="+")
    ap.add_argument("--out", default="runs/narrow/analysis.json")
    a = ap.parse_args()
    rows = []
    for js in a.launches:
        J = json.load(open(js))
        z = np.load(J["npz"])
        plaq = z["plaq"].astype(np.float64)                  # (P, 2, nplaq)
        specs = z["specs"]                                    # (P, 9): s, o, shift x4, kind, which, theta
        d = z["d"]
        n_shell = len(z["shell"])
        nB = len(z["dyn_lids"])
        for m in J["instances"]:
            f = m["first_pair"]
            blk = slice(f, f + 80)
            P_ = plaq[blk]
            kind = specs[blk, 6]
            k = np.abs(P_[:, 0] - P_[:, 1]).max(axis=-1) / 2.0                  # (80,)
            # null: chain A start 0 vs chain A start 1, same perturbation index
            nullv = np.abs(P_[:40, 0] - P_[40:, 0]).max(axis=-1) / 2.0           # (40,)
            null = np.concatenate([nullv, nullv])
            res = dict(launch=js, beta=J["beta"], yclass=m["yclass"], pool=m["pool"], job=m["job"])
            for s in (0, 1):
                sl = slice(40 * s, 40 * s + 40)
                ks, ns_, kd = k[sl], null[sl], kind[sl]
                zsel = kd == 1
                ysel = kd == 2
                kz = ks[zsel]
                kz_sub = np.maximum(ks[zsel] - ns_[zsel], 0.0)
                scale = n_shell / zsel.sum() / nB
                R = scale * kz.sum()
                Rs = scale * kz_sub.sum()
                nz = len(kz)
                jk = np.array([scale * nz / (nz - 1) * np.delete(kz_sub, i).sum() for i in range(nz)])
                se = math.sqrt((nz - 1) / nz * np.sum((jk - jk.mean()) ** 2))
                kdiff = ks[zsel] - ns_[zsel]
                Rd = scale * kdiff.sum()
                jd = np.array([scale * nz / (nz - 1) * np.delete(kdiff, i).sum() for i in range(nz)])
                sed = math.sqrt((nz - 1) / nz * np.sum((jd - jd.mean()) ** 2))
                res[f"start{s}"] = dict(R_low=R, R_low_sub=Rs, R_low_sub_se=se, R_low_diff=Rd, R_low_diff_se=sed, k_low_mean=float(kz.mean()),
                                        null_mean=float(ns_[zsel].mean()), kY_mean=float(ks[ysel].mean()) if ysel.any() else None,
                                        kY_sub_mean=float(np.maximum(ks[ysel] - ns_[ysel], 0).mean()) if ysel.any() else None,
                                        dis_plateau=float(d[-3:, f + 40 * s:f + 40 * s + 40].mean()) / nB)
            rows.append(res)
    # verdicts
    out = dict(rows=rows, verdicts={})
    for beta in sorted({r["beta"] for r in rows}):
        samp = [r for r in rows if r["beta"] == beta and r["yclass"] == "sampled"]
        adv = [r for r in rows if r["beta"] == beta and r["yclass"] != "sampled"]

        def fails(r):
            return any(r[f"start{s}"]["R_low_sub"] - 2 * r[f"start{s}"]["R_low_sub_se"] >= 1.0 for s in (0, 1))

        wls = "FAILS" if samp and all(fails(r) for r in samp) else "UNRESOLVED"
        wlq = [f"{r['yclass']}/pool{r['pool']}" for r in adv if fails(r)]
        out["verdicts"][str(beta)] = dict(WL_S=wls, WL_Q_refuted_by=wlq, WL_Q="REFUTED" if wlq else "not refuted",
                                          R_low_sub_sampled=[round(float(r["start0"]["R_low_sub"]), 4) for r in samp],
                                          R_low_diff_sampled=[(round(float(r["start0"]["R_low_diff"]), 4),
                                                               round(float(r["start0"]["R_low_diff_se"]), 4)) for r in samp],
                                          R_low_sub_adversarial={f"{r['yclass']}/pool{r['pool']}":
                                                                 round(float(r["start0"]["R_low_sub"]), 4) for r in adv},
                                          R_low_diff_adversarial={f"{r['yclass']}/pool{r['pool']}":
                                                                  (round(float(r["start0"]["R_low_diff"]), 4),
                                                                   round(float(r["start0"]["R_low_diff_se"]), 4)) for r in adv})
    json.dump(out, open(a.out, "w"), indent=1)
    for beta, v in out["verdicts"].items():
        print(f"beta {beta}: WL-S {v['WL_S']}; WL-Q {v['WL_Q']} {v['WL_Q_refuted_by']}")
        print(f"   R_low_sub sampled (start 0): {v['R_low_sub_sampled']}")
        print(f"   R_low_sub adversarial (start 0): {v['R_low_sub_adversarial']}")
        print(f"   R_low_diff (start 0) sampled: {v['R_low_diff_sampled']}; adversarial: {v['R_low_diff_adversarial']}")


if __name__ == "__main__":
    main()
