"""Evaluate the CPU pilot checks against PREREG-PILOT.md (amendments 1, 2 and 3; amendment 2: jackknife replica errors and the
t_{K-1} 95.45 % factor in place of 2). Updated before the run-3 data.
  py pilot_eval.py E1 pilot_E1_run2.json
  py pilot_eval.py E2 pilot_E2.log          (the JSON lines of the five runs and the three analyses, in run_pilot.sh order)
  py pilot_eval.py P pilot_P.log
Prints each criterion with its numbers and PASS/FAIL, and the overall verdict."""
import json
import math
import sys

import numpy as np

EX = {"tv": 0.0703146985768639, "kr_upper": 0.09589768508666131, "jbar": 0.342}


def verdict(rows):
    ok = True
    for name, good, detail in rows:
        print(f"  {'PASS' if good else 'FAIL'}  {name}: {detail}")
        ok &= bool(good)
    print("OVERALL", "PASS" if ok else "FAIL")
    return 0 if ok else 1


def e1(path):
    d = json.load(open(path))
    R = d["rows"]
    tv = np.array([r["est"]["tv"] for r in R])
    sb = np.array([r["sd_tv"] for r in R])
    nu = np.array([r["null_tv"] for r in R])
    jb = np.array([r["est"]["jbar"] for r in R])
    kr = np.array([r["est"]["kr_upper"] for r in R])
    sdr = tv.std(ddof=1)
    tq = np.array([r.get("t", 2.0) for r in R])
    n1 = int((np.abs(tv - EX["tv"]) <= tq * sb).sum())
    rows = [
        (f"1 |TV_hat - exact| <= t sigma (t = {tq[0]:.3f}, {R[0].get('error', 'bootstrap')}) in >= 9 of 10", n1 >= 9, f"{n1}/10"),
        ("2 mean within 2 sd/sqrt(10)", abs(tv.mean() - EX["tv"]) <= 2 * sdr / math.sqrt(len(tv)),
         f"mean {tv.mean():.5f} vs {EX['tv']:.5f}, |diff| {abs(tv.mean() - EX['tv']):.5f}, allowed {2 * sdr / math.sqrt(len(tv)):.5f}"),
        ("3a sigma in [0.0009, 0.0024] (amendment 1)", sb.min() >= 0.0009 and sb.max() <= 0.0024,
         f"range [{sb.min():.5f}, {sb.max():.5f}]"),
        ("3b sigma / sd over reps in [0.6, 1.6]", 0.6 <= sb.mean() / sdr <= 1.6, f"{sb.mean() / sdr:.2f} (sd {sdr:.5f})"),
        ("4 mean null TV <= 0.01", nu.mean() <= 0.01, f"{nu.mean():.5f}"),
        ("5a Jbar within 2 sd in >= 9 of 10", (np.abs(jb - EX["jbar"]) <= 2 * jb.std(ddof=1)).sum() >= 9,
         f"{int((np.abs(jb - EX['jbar']) <= 2 * jb.std(ddof=1)).sum())}/10, mean {jb.mean():.4f}"),
        ("5b KR_upper within 2 sd in >= 9 of 10", (np.abs(kr - EX["kr_upper"]) <= 2 * kr.std(ddof=1)).sum() >= 9,
         f"{int((np.abs(kr - EX['kr_upper']) <= 2 * kr.std(ddof=1)).sum())}/10, mean {kr.mean():.5f}"),
    ]
    return verdict(rows)


def c1(path):
    d = json.load(open(path))
    n, t = d["null"], d["true"]
    lim = 2.6 / math.sqrt(d["draws"])
    rows = [
        ("i null: spread / floor in [0.90, 1.10]", 0.90 <= n["ratio_sd_floor"] <= 1.10, f"{n['ratio_sd_floor']:.3f} (sd {n['sd']:.5f}, floor {n['floor']:.5f})"),
        ("i true: spread / floor in [0.90, 1.10]", 0.90 <= t["ratio_sd_floor"] <= 1.10, f"{t['ratio_sd_floor']:.3f} (sd {t['sd']:.5f}, floor {t['floor']:.5f})"),
        ("ii null mean within 2.6 sd/sqrt(200) of 0", abs(n["mean"]) <= lim * n["sd"], f"{n['mean']:.5f} (allowed {lim * n['sd']:.5f})"),
        ("ii true mean within 2.6 sd/sqrt(200) of 0.02784", abs(t["mean"] - t["exact"]) <= lim * t["sd"],
         f"{t['mean']:.5f} vs {t['exact']:.5f} (allowed {lim * t['sd']:.5f})"),
    ]
    print(f"  info (iii): mean jackknife / spread: null {n['ratio_jk_sd']:.2f}, true {t['ratio_jk_sd']:.2f}")
    return verdict(rows)


def jsonlines(path):
    out = []
    for line in open(path, encoding="utf-8", errors="replace"):
        line = line.strip()
        if line.startswith("{"):
            out.append(json.loads(line))
    return out


def e2(path):
    J = jsonlines(path)
    runs = [j for j in J if "out" in j]
    an = [j for j in J if "tv" in j]
    assert len(runs) == 5 and len(an) == 3, (len(runs), len(an))
    a, b, c, dd, e = runs
    ab, cd, ce = an
    acc_ok = all(r["acc"] >= 0.6 for r in runs)
    ry = [(b["resid_y"], 3 / 200), (dd["resid_y"], 3 / 800)]
    t = max(ab.get("t", 2.0), cd.get("t", 2.0), ce.get("t", 2.0))
    tv_inf = (4 * cd["tv"] - ab["tv"]) / 3
    s_inf = math.sqrt(16 * cd["sd_tv"] ** 2 + ab["sd_tv"] ** 2) / 3
    jb_inf = (4 * cd["jbar"] - ab["jbar"]) / 3
    jb_sig = math.sqrt(16 * cd["sd_jbar"] ** 2 + ab["sd_jbar"] ** 2) / 3
    D2EX = 0.027842832345280916
    d2_inf = (4 * cd["d2_U"] - ab["d2_U"]) / 3
    d2_sig = math.sqrt(16 * cd["sd_d2"] ** 2 + ab["sd_d2"] ** 2) / 3
    rows = [
        ("1a acceptance >= 0.6 in every run", acc_ok, ", ".join(f"{r['acc']:.2f}" for r in runs)),
        ("1b resid_y < 3/kappa in the flip runs", all(v < lim for v, lim in ry),
         ", ".join(f"{v:.4f} < {lim:.4f}" for v, lim in ry)),
        (f"2 TV_inf within t sigma_inf of 0.07031 (t = {t:.3f})", abs(tv_inf - EX["tv"]) <= t * s_inf,
         f"TV_200 {ab['tv']:.5f}, TV_800 {cd['tv']:.5f}, TV_inf {tv_inf:.5f} +- {s_inf:.5f}"),
        (f"3 Jbar_inf within t sigma_inf of 0.342 (t = {t:.3f})", abs(jb_inf - EX["jbar"]) <= t * jb_sig,
         f"Jbar_200 {ab['jbar']:.4f}, Jbar_800 {cd['jbar']:.4f}, Jbar_inf {jb_inf:.4f} +- {jb_sig:.4f}"),
        ("4 (amendment 3) null TV (c, e) below the 95 % quantile of the simulated null at N/(2 tau)", ce["tv"] <= ce["null_q95"],
         f"{ce['tv']:.5f} vs q95 {ce['null_q95']:.5f} (sim mean {ce['null_mean_sim']:.5f}, n_eff {ce['null_n_eff']})"),
        (f"5 null D2_U (c, e) consistent with 0 (t7 = {ce['t_d2']:.3f})", abs(ce["d2_U"]) <= ce["t_d2"] * ce["sd_d2"],
         f"{ce['d2_U']:.5f} +- {ce['sd_d2']:.5f}"),
        ("6 D2_inf within t7 sigma_inf of 0.02784", abs(d2_inf - D2EX) <= ab["t_d2"] * d2_sig,
         f"D2_200 {ab['d2_U']:.5f}, D2_800 {cd['d2_U']:.5f}, D2_inf {d2_inf:.5f} +- {d2_sig:.5f}; C_D_inf {0.5 * math.sqrt(max(d2_inf, 0)):.4f} (exact 0.0834)"),
        ("7 floor anchoring sigma_jk(D2) >= 0.491 sigma_floor(D2), three pairs",
         all(x["sd_d2"] >= 0.491 * x["d2_floor"] for x in (ab, cd, ce)),
         ", ".join(f"{x['sd_d2']:.5f} vs 0.491 x {x['d2_floor']:.5f}" for x in (ab, cd, ce))),
    ]
    print("  info: tau_int", [x["tauint"] for x in an], "resid", [r["resid"] for r in runs])
    return verdict(rows)


def p(path):
    J = jsonlines(path)
    runs = [j for j in J if "out" in j]
    an = [j for j in J if "tv" in j]
    assert len(runs) == 3 and len(an) == 2, (len(runs), len(an))
    a, b, c = runs
    ab, ac = an
    tau = max(max(x["tauint"].values()) for x in an)
    diff = ab["tv"] - ac["tv"]
    sig = math.sqrt(ab["sd_tv"] ** 2 + ac["sd_tv"] ** 2)
    t = max(ab.get("t", 2.0), ac.get("t", 2.0))
    rows = [
        ("1 acceptance >= 0.6 after tuning", all(r["acc"] >= 0.6 for r in runs), ", ".join(f"{r['acc']:.2f}" for r in runs)),
        ("2 resid_y < 0.05 (flip run), constraint residual < 0.05", b["resid_y"] < 0.05 and all(r["resid"] < 0.05 for r in runs),
         f"resid_y {b['resid_y']:.4f}; resid " + ", ".join(f"{r['resid']:.4f}" for r in runs)),
        ("3 tau_int finite and < 15", math.isfinite(tau) and tau < 15, f"{tau:.2f}"),
        (f"4 TV(none, flip) - TV(none, null) within t sigma of 0 (t = {t:.3f}; time-block replicas)", abs(diff) <= t * sig,
         f"{diff:.5f} +- {sig:.5f}"),
    ]
    for r in runs:
        print(f"  info: eps {r['eps']}, nleap {r['nleap']}, n_meas {r['n_meas']}, wall {r['wall_s']:.0f} s, stopped {r['stopped_at']}")
    return verdict(rows)


if __name__ == "__main__":
    sys.exit({"E1": e1, "E2": e2, "P": p, "C1": c1}[sys.argv[1]](sys.argv[2]))
