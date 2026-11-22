"""Cycle 3, workstream 2 (c3b-refit): choice of the smearing weight w of the good blocking from the one-loop check.

Pre-registered in PREREG.md, section "The weight w" (rule written before this script was run). Reuses workstream 1's linearised,
abelian flux-variance code (../ws1-routeA/selfenergy.py, imported read-only) on a grid of weights. CPU only, seconds.

Usage: python wscan.py [--out wscan.json]
"""
import argparse
import importlib.util
import json
import os
import time

os.environ["CUDA_VISIBLE_DEVICES"] = "-1"
HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("selfenergy", os.path.join(HERE, "..", "ws1-routeA", "selfenergy.py"))
SE = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(SE)

W_GRID = (0.0, 0.25, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0, 4.0)
Z2_TIES = (1 / 6, 0.25, 0.5)  # weights at which a Z2 path sum can vanish (s0 + w * even integer = 0)
LEVELS = (2, 3, 4)  # ell = 4, 8, 16


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=os.path.join(HERE, "wscan.json"))
    a = ap.parse_args()
    t0 = time.time()
    res = {}
    for w in W_GRID:
        for (mu, nu, name) in ((0, 1, "ts"), (1, 2, "ss")):
            for level in LEVELS:
                ell = 2 ** level
                L = 4 * ell if level < 4 else 3 * ell
                s2 = SE.variance(SE.plaquette_current(level, mu, nu, w), L)
                res[f"{w}|{name}|{ell}"] = s2
                print(f"w={w:<5} {name} ell={ell:2d} L={L} sigma2={s2:.5f}  ({time.time() - t0:.0f}s)", flush=True)
    # the pre-registered rule (PREREG.md): smallest grid weight, not a Z2 tie weight, whose sigma2(16) is within 5 % of the grid
    # minimum for both orientations, and whose ratio sigma2(16) / sigma2(8) <= 1.0 for both (no residual growth)
    mins = {o: min(res[f"{w}|{o}|16"] for w in W_GRID) for o in ("ts", "ss")}
    chosen = None
    rows = []
    for w in W_GRID:
        ok_min = all(res[f"{w}|{o}|16"] <= 1.05 * mins[o] for o in ("ts", "ss"))
        ok_flat = all(res[f"{w}|{o}|16"] <= res[f"{w}|{o}|8"] for o in ("ts", "ss"))
        tie = any(abs(w - z) < 1e-12 for z in Z2_TIES)
        rows.append({"w": w, "ts16": res[f"{w}|ts|16"], "ss16": res[f"{w}|ss|16"], "within5pc": ok_min, "flat": ok_flat, "z2_tie": tie})
        if chosen is None and ok_min and ok_flat and not tie and w > 0:
            chosen = w
    print("\nw      sigma2_ts(16) sigma2_ss(16) within5% flat z2tie")
    for r in rows:
        print(f"{r['w']:<6} {r['ts16']:.4f}        {r['ss16']:.4f}        {r['within5pc']!s:<8} {r['flat']!s:<5} {r['z2_tie']}")
    print(f"grid minima: ts {mins['ts']:.4f}, ss {mins['ss']:.4f}; CHOSEN w = {chosen}")
    json.dump({"sigma2": res, "rows": rows, "minima": mins, "chosen_w": chosen}, open(a.out, "w"), indent=1)


if __name__ == "__main__":
    main()
