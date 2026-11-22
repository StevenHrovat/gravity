# NT' check (NO-TRAP.md 4): with the Z2 label chosen once at the root (the sign pattern that minimises the largest
# corrected relative angle), does the corrected star stay away from the logarithm's cut (relative angle pi) along its
# orbit under Balaban's star map? Stars: Haar-random, and the slow deep stars found by the adversarial search.
# Reports the largest corrected relative angle at the root and along 40 steps (the cut is 180 degrees).
import sys, os, itertools
import numpy as np
NH = int(sys.argv[1]) if len(sys.argv) > 1 else 5000
sys.argv = sys.argv[:1] + ["40", "1", "11"]
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "notrap_search.py"), encoding="utf-8").read()
src = src.split("# ---------- NT1 ----------")[0]
ns = {"__file__": os.path.abspath(__file__)}; exec(compile(src, "notrap_search.py", "exec"), ns)
qmul, qinv, qexp, step04, n, haar, capture_times, rng = (ns[k] for k in
    ("qmul", "qinv", "qexp", "step04", "n", "haar", "capture_times", "rng"))
SIGNS = np.array([(1,) + s for s in itertools.product((1, -1), repeat=n - 1)], float)   # mod global sign


def maxangle(g):
    rel = qmul(g[:, :, None, :], qinv(g[:, None, :, :]))
    return np.degrees(np.arccos(np.clip(rel[..., 0], -1, 1))).max((1, 2))


def best_label(g):
    best = np.full(g.shape[0], 1e9); out = np.ones(g.shape[:2])
    for s in SIGNS:
        m = maxangle(g * s[None, :, None])
        b = m < best; best[b] = m[b]; out[b] = s
    return out, best


def orbit_max(h, steps=40):
    mx = maxangle(h)
    for _ in range(steps):
        h = step04(h, False); mx = np.maximum(mx, maxangle(h))
    return mx


g = haar(NH)
sig, root = best_label(g)
h = g * sig[..., None]
om = orbit_max(h)
print(f"Haar stars ({NH}): corrected max angle at the root: max {root.max():.1f} deg, median {np.median(root):.1f}; "
      f"along the orbit: max {om.max():.1f} deg; fraction above 170: {np.mean(om > 170):.4f}")
# slow deep stars: a short adversarial search as in notrap_longsearch.py, then the same check
G = haar(60); t = capture_times(G); s = np.full(60, 0.3)
for it in range(150):
    cand = qmul(qexp(s[:, None, None] * rng.normal(size=G.shape[:-1] + (3,))), G)
    tc = capture_times(cand); better = tc >= t
    G[better] = cand[better]; t[better] = tc[better]; s = np.where(better, s * 1.1, s * 0.8).clip(1e-6, 1)
sig, root = best_label(G)
om = orbit_max(G * sig[..., None])
print(f"slow deep stars (60, capture times up to {t.max()}): corrected max angle at the root: max {root.max():.1f}; "
      f"along the orbit: max {om.max():.1f} deg")
