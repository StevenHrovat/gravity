"""PREREG run 2 (design, float only): bound B1 over the eigenvalue simplex, and the exact symmetric formula over symmetric
configurations (ceiling). Chooses the beta values and the ceiling configuration for the certified runs.
Eigenvalues of Q: kappa * s, s >= 0, sum s = 6 (kappa = 4 b_A / 3). For b_A < 0 the same law is exp(|kappa| t . x) with
t = 6 - s (t_i in [0, 6], sum t = 18), up to normalisation."""
import json
import math
import os

os.environ.setdefault("CUDA_VISIBLE_DEVICES", "-1")
import numpy as np

import bingham as bg
from checks import sym_formula  # noqa: E402  (re-runs nothing heavy: checks.py is import-guarded below)


def simplex(step):
    pts = []
    n = int(round(6 / step))
    for a in range(n + 1):
        for b in range(a + 1):
            for c in range(b + 1):
                d = n - a - b - c
                if 0 <= d <= c:
                    pts.append((a * step, b * step, c * step, d * step))
    return np.array(pts)


S = simplex(0.25)
out = {}
for bA in (0.05, 0.1, 0.15, 0.2, 0.22, 0.24, 0.26, 0.3, -0.05, -0.1, -0.2, -0.3, -0.4):
    k = abs(4 * bA / 3)
    lam = k * (S if bA > 0 else 6 - S)
    N, Pm, Dm, zeta, s2, Vh = bg.b1_float(lam)
    i = int(np.argmax(N))
    col = 48 * abs(bA) * N[i]
    out[bA] = dict(N=float(N[i]), s=S[i].tolist(), col=float(col), zeta=float(zeta.max()), s2=float(s2.max()), Vh=float(Vh.max()))
    print(f"b_A = {bA:+.2f}: sup B1 = {N[i]:.5f} at s = {S[i]}, column 48|b|N = {col:.4f};  zeta max {zeta.max():.4f},"
          f" sigma(2L) max {s2.max():.4f}, Vh max {Vh.max():.5f}", flush=True)
# symmetric configurations: a, b eigenvectors; s_a >= 1 (a is a staple), s_a + s_b + s3 + s4 = 6
print("symmetric formula (exact N_A at Klein-symmetric configurations):")
for bA in (0.2, 0.25, 0.28, -0.3, -0.5):
    k = 4 * bA / 3
    best = None
    for sa in np.arange(1, 6.01, 0.5):
        for sb in np.arange(0, 6.01 - sa, 0.5):
            rest = 6 - sa - sb
            for s3 in np.arange(0, rest + 0.01, max(rest / 2, 0.5)):
                s4 = rest - s3
                v = sym_formula(k * sa, k * sb, k * s3, k * s4)
                if best is None or v > best[0]:
                    best = (v, (sa, sb, s3, s4))
    print(f"  b_A = {bA:+.2f}: max over symmetric grid {best[0]:.5f} at (s_a, s_b, s3, s4) = {best[1]}, column {48 * abs(bA) * best[0]:.4f}",
          flush=True)
json.dump({str(k): v for k, v in out.items()}, open("explore.json", "w"), indent=1)
