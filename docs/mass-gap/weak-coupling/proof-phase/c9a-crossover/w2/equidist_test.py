"""EXPLORATORY equidistribution test (EQUIDIST.md section 1, rule fixed before the beta 3.5, L >= 4 ratios were looked at).
Single-sector deficit delta(L) = 1 - r(L) on the cubic tori L^4, L = 2, 4, 6; slope of log delta on log L.

Usage: py equidist_test.py [--out runs/equidist_test.json]
"""
import argparse
import json
import math
import os

import numpy as np

import smalltorus as S


def log_r(L, T, beta):
    lr, var = 0.0, 0.0
    for m in range(1, L * L + 1):
        fn = S.fname("snake", L, T, beta, m)
        if not os.path.exists(fn):
            return None
        rec = json.load(open(fn))
        em, ep = np.array(rec["bins_em"]), np.array(rec["bins_ep"])
        v, s = S.jk_stats(lambda x: math.log(x[0]) - math.log(x[1]), [em, ep])
        lr += v
        var += s * s
    return lr, math.sqrt(var)


def classify(pts):
    """pts: list of (L, delta, sigma_delta); WLS of log delta on log L over points with delta > 2 sigma."""
    use = [(L, d, s) for (L, d, s) in pts if d > 2 * s]
    if len(use) < 2:
        return dict(n_used=len(use), slope=None, sigma_slope=None, cls="unresolved")
    x = np.log([u[0] for u in use])
    y = np.log([u[1] for u in use])
    w = np.array([(u[1] / u[2]) ** 2 for u in use])  # 1 / var(log delta)
    W = np.sum(w)
    xm, ym = np.sum(w * x) / W, np.sum(w * y) / W
    sxx = np.sum(w * (x - xm) ** 2)
    s = float(np.sum(w * (x - xm) * (y - ym)) / sxx)
    ss = float(math.sqrt(1 / sxx))
    if -1.5 <= s <= -0.5:
        cls = "floor-like (square-root type)"
    elif s < -1.5 and s + 2 * ss < -0.5:
        cls = "faster than a floor"
    elif s > -0.5 and s - 2 * ss > -1.5:
        cls = "no decrease"
    else:
        cls = "unresolved"
    return dict(n_used=len(use), slope=s, sigma_slope=ss, cls=cls)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="runs/equidist_test.json")
    a = ap.parse_args()
    out = {}
    for beta in (2.3, 3.5):
        pts, pts_floor, rows = [], [], []
        for L in (2, 4, 6):
            res = log_r(L, L, beta)
            if res is None:
                continue
            lr, slr = res
            r = math.exp(lr)
            d = 1 - r
            sd = r * slr
            sd_floor = r * max(slr, 1.0)
            rows.append(dict(L=L, r=r, log_r=lr, sig_log_r=slr, delta=d, sig_delta=sd, sig_delta_floor=sd_floor))
            pts.append((L, d, sd))
            pts_floor.append((L, d, sd_floor))
        out[str(beta)] = dict(rows=rows, stat=classify(pts), floor=classify(pts_floor))
        print(beta, json.dumps(out[str(beta)]), flush=True)
    json.dump(out, open(a.out, "w"), indent=1)


if __name__ == "__main__":
    main()
