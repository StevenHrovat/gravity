"""Analyse the centre-vortex runs against PREREG-VORTEX.md.

    python analyse_vortex.py runs-gpu/vortex_b2.3_L12.npz [runs-gpu/vortex_b2.4_L16.npz ...]

Errors: jackknife over configurations. Consecutive configurations come from the same chains 20 sweeps apart, so they can be
correlated; the jackknife is done with bins of 1, 5 and 10 configurations and the largest error is used (the conservative choice,
stated here before the analysis; bin size 1 is the plain jackknife the pre-registration names).
Criterion 1 is judged on the central values (|chi_proj / chi_full - 1| <= 0.30), with the error of the ratio reported beside it.
"""
import json
import sys

import numpy as np


def creutz(W):
    r = np.arange(2, W.shape[-1])
    with np.errstate(invalid="ignore", divide="ignore"):
        return -np.log(W[..., r, r] * W[..., r - 1, r - 1] / (W[..., r, r - 1] * W[..., r - 1, r]))  # index 0 is R = 2


def jackknife(samples, f, bins):
    n = (len(samples) // bins) * bins
    s = samples[:n].reshape(n // bins, bins, *samples.shape[1:]).mean(axis=1)
    m = len(s)
    full = f(s.mean(axis=0))
    leave = np.array([f((s.sum(axis=0) - s[i]) / (m - 1)) for i in range(m)])
    err = np.sqrt((m - 1) / m * np.sum((leave - leave.mean(axis=0)) ** 2, axis=0))
    return full, err


def est(samples, f):
    vals = [jackknife(samples, f, b) for b in (1, 5, 10)]
    return vals[0][0], np.nanmax(np.array([v[1] for v in vals]), axis=0)


def analyse(path):
    d = np.load(path)
    full, proj, rem, ctrl = (d[k] for k in ("full", "proj", "removed", "proj_nogauge"))
    n = len(full)
    out = {"file": path, "beta": float(d["beta"]), "L": int(d["L"]), "configurations": n, "partial": int(d["partial"]),
           "vortex_density": float(np.mean(d["vortex_density"])), "R": {}}
    both = np.stack([full, proj], axis=1)
    both_rem = np.stack([full, rem], axis=1)
    for R in (3, 4):
        i = R - 2
        cf, ef = est(full, lambda W: creutz(W)[i])
        cp_, ep = est(proj, lambda W: creutz(W)[i])
        cr, er = est(rem, lambda W: creutz(W)[i])
        rat, erat = est(both, lambda W: creutz(W[1])[i] / creutz(W[0])[i])
        rrat, errat = est(both_rem, lambda W: creutz(W[1])[i] / creutz(W[0])[i])
        c1 = bool(abs(rat - 1) <= 0.30)
        c2 = bool(rrat < 0.20 or abs(cr) <= 2 * er)
        out["R"][R] = {"chi_full": [cf, ef], "chi_proj": [cp_, ep], "chi_removed": [cr, er], "proj_over_full": [rat, erat],
                       "removed_over_full": [rrat, errat], "criterion1": c1, "criterion2": c2}
    # control: projected loops without gauge fixing, R, T >= 2, consistent with zero within 2 errors
    wc, ec = est(ctrl, lambda W: W[2:, 2:])
    z = np.abs(wc) / ec
    out["control"] = {"max_abs_W_over_err_RT_ge_2": float(np.max(z)), "W_2_2": [float(wc[0, 0]), float(ec[0, 0])],
                      "criterion3": bool(np.all(z <= 2))}
    # follow-up (PREREG-VORTEX-SIGMA.md, post-hoc): R = 4, 5 against the torelon string tension of the TTL scan
    sig = SIGMA.get(round(out["beta"], 2))
    if sig is not None:
        fu = {"sigma_a2": sig, "R": {}}
        for R in (4, 5):
            i = R - 2
            cp_, ep = est(proj, lambda W: creutz(W)[i])
            cr, er = est(rem, lambda W: creutz(W)[i])
            rat = cp_ / sig[0]
            erat = rat * np.hypot(ep / cp_, sig[1] / sig[0])
            noisy = bool(ep / abs(cp_) > 0.5)
            f1 = bool(abs(rat - 1) <= 0.30 and not noisy)
            f2 = bool(cr < 0.20 * sig[0] or abs(cr) <= 2 * er)
            fu["R"][R] = {"chi_proj": [cp_, ep], "chi_removed": [cr, er], "proj_over_sigma": [rat, erat], "too_noisy": noisy,
                          "f1": f1, "f2": f2}
        fu["pass"] = bool(all(x["f1"] and x["f2"] for x in fu["R"].values()))
        out["followup"] = fu
    out["pass"] = bool(all(out["R"][R]["criterion1"] and out["R"][R]["criterion2"] for R in (3, 4)) and out["control"]["criterion3"])
    return out


# sigma a^2 = (a sqrt(sigma))^2 from the TTL scan's torelons (error: 2 x relative error of a sqrt(sigma))
SIGMA = {round(x["beta"], 2): (x["a_sqrt_sigma"][0] ** 2, 2 * x["a_sqrt_sigma"][0] * x["a_sqrt_sigma"][1])
         for x in json.load(open("../results/ttl_summary.json"))}


def fmt(v):
    return f"{v[0]:.3f} ± {v[1]:.3f}"


if __name__ == "__main__":
    res = [analyse(p) for p in sys.argv[1:]]
    for r in res:
        print(f"beta {r['beta']} L {r['L']}: {r['configurations']} configurations{' (PARTIAL)' if r['partial'] else ''}, "
              f"vortex density {r['vortex_density']:.4f}")
        for R, x in r["R"].items():
            print(f"  R={R}: chi full {fmt(x['chi_full'])}  proj {fmt(x['chi_proj'])}  removed {fmt(x['chi_removed'])}  "
                  f"proj/full {fmt(x['proj_over_full'])} [{'pass' if x['criterion1'] else 'FAIL'}]  "
                  f"removed/full {fmt(x['removed_over_full'])} [{'pass' if x['criterion2'] else 'FAIL'}]")
        c = r["control"]
        print(f"  control: W(2,2) {fmt(c['W_2_2'])}, max |W|/err over R,T>=2 = {c['max_abs_W_over_err_RT_ge_2']:.2f} "
              f"[{'pass' if c['criterion3'] else 'FAIL'}]")
        print(f"  => {'pass' if r['pass'] else 'FAIL'} (PREREG-VORTEX.md)")
        if "followup" in r:
            fu = r["followup"]
            print(f"  follow-up (post-hoc, PREREG-VORTEX-SIGMA.md), sigma a^2 = {fmt(fu['sigma_a2'])}:")
            for R, x in fu["R"].items():
                print(f"    R={R}: proj {fmt(x['chi_proj'])}, proj/sigma {fmt(x['proj_over_sigma'])}{' TOO NOISY' if x['too_noisy'] else ''} "
                      f"[{'pass' if x['f1'] else 'FAIL'}]  removed {fmt(x['chi_removed'])} [{'pass' if x['f2'] else 'FAIL'}]")
            print(f"    => follow-up {'pass' if fu['pass'] else 'FAIL'}")
    json.dump(res, open("../results/vortex_summary.json", "w"), indent=1, default=float)
