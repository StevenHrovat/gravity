"""The pre-registered photon test (PREREG.md, U(1) part) on the output of analyse.py.

Coulomb phase (beta = 1.2): E1 at each L within 2 errors of the free massless value; a fit E1^2 = m^2 + E_free^2 over the boxes gives m
consistent with 0 within 2 errors (fail if more than 3 errors above 0). Confined phase (beta = 0.8): E1(L=12) / E1(L=8) > 0.85, or no
cosh solution (reported as "E1 above about 2").

Usage: python photon_test.py summary.json
"""

import json
import sys

import numpy as np


def main(path):
    rows = [r for r in json.load(open(path, encoding="utf-8")) if r.get("group") == "U(1)"]
    out = {}
    coul = sorted([r for r in rows if abs(r["beta"] - 1.2) < 1e-9], key=lambda r: r["L"])
    print("Coulomb phase, beta = 1.2")
    x, dx, f = [], [], []
    for r in coul:
        e, de = r["E_p1_used"]
        ef = r["E_free_p1"]
        dev = (e - ef) / de if de > 0 else float("nan")
        print(f"  L={r['L']:2d}  E1 = {e:.3f} +- {de:.3f}  free {ef:.3f}  deviation {dev:+.1f} errors  E1*L = {e * r['L']:.2f}")
        x.append(e); dx.append(de); f.append(ef)
    x, dx, f = map(np.array, (x, dx, f))
    # m^2 = E1^2 - E_free^2 per box, combined by inverse variance
    m2 = x ** 2 - f ** 2
    dm2 = 2 * x * dx
    w = 1 / dm2 ** 2
    m2bar = float(np.sum(w * m2) / np.sum(w))
    dm2bar = float(1 / np.sqrt(np.sum(w)))
    print(f"  fitted m^2 = {m2bar:+.4f} +- {dm2bar:.4f}  ({m2bar / dm2bar:+.1f} errors from 0)")
    ok_boxes = bool(np.all(np.abs(x - f) <= 2 * dx))
    verdict = "pass" if ok_boxes and abs(m2bar) <= 2 * dm2bar else ("fail" if m2bar > 3 * dm2bar else "tension")
    print(f"  verdict: {verdict}")
    out["coulomb"] = {"boxes": [{"L": r["L"], "E1": r["E_p1_used"], "E_free": r["E_free_p1"]} for r in coul],
                      "m2": [m2bar, dm2bar], "verdict": verdict}
    conf = {r["L"]: r for r in rows if abs(r["beta"] - 0.8) < 1e-9}
    print("Confined phase, beta = 0.8")
    for L, r in sorted(conf.items()):
        print(f"  L={L:2d}  E1 = {r['E_p1_used'][0]:.3f} +- {r['E_p1_used'][1]:.3f}  (free massless would be {r['E_free_p1']:.3f})")
    if 8 in conf and 12 in conf:
        e8, e12 = conf[8]["E_p1_used"][0], conf[12]["E_p1_used"][0]
        if not (np.isfinite(e8) and np.isfinite(e12)):
            v = "pass (no cosh solution: E1 above about 2)"
            ratio = None
        else:
            ratio = e12 / e8
            v = "pass" if ratio > 0.85 else "fail"
        print(f"  E1(12)/E1(8) = {ratio}  (massless: {8 / 12:.2f}); verdict: {v}")
        out["confined"] = {"ratio": ratio, "verdict": v}
    print(json.dumps(out))


if __name__ == "__main__":
    main(sys.argv[1])
