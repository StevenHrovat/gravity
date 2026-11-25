# Adversarial checks of Lemma NT' (NO-TRAP.md 4). Usage: python -I cut_adversarial.py [mode: 12 | 3 | 4]
#  (i)   root bound: maximise, over 8-point stars, the best-label corrected max relative angle.
#  (ii)  one step: maximise (max corrected angle after one step) - (before), corrected stars with the best label.
#  (iii) worst orbit: maximise the largest corrected relative angle along a 30-step orbit, label fixed at the root.
#  (iv)  near-cut episodes: maximise the number of steps (of 30) at which the corrected max angle exceeds 160 deg.
import sys, os
import numpy as np
MODE = sys.argv[1] if len(sys.argv) > 1 else "12"
sys.argv = sys.argv[:1] + ["40", "1", "13"]
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "cut_avoidance.py"), encoding="utf-8").read()
src = src.split("g = haar(NH)")[0].replace("NH = int(sys.argv[1]) if len(sys.argv) > 1 else 5000", "NH = 1")
ns = {"__file__": os.path.abspath(__file__)}; exec(compile(src, "cut_avoidance.py", "exec"), ns)
qmul, qexp, step04, haar, rng, maxangle, best_label = (ns[k] for k in ("qmul", "qexp", "step04", "haar", "rng", "maxangle", "best_label"))
M = 200


def climb(objective, g, iters=150, s0=0.3):
    val = objective(g); s = np.full(g.shape[0], s0)
    for _ in range(iters):
        cand = qmul(qexp(s[:, None, None] * rng.normal(size=g.shape[:-1] + (3,))), g)
        v = objective(cand); b = v >= val
        g[b] = cand[b]; val[b] = v[b]; s = np.where(b, s * 1.1, s * 0.8).clip(1e-6, 1)
    return g, val


def growth(x):
    sig, a0 = best_label(x)
    return maxangle(step04(x * sig[..., None], False)) - a0


def orbitmax(x, steps=30):
    sig, _ = best_label(x); hcor = x * sig[..., None]; mx = maxangle(hcor)
    for _ in range(steps):
        hcor = step04(hcor, False); mx = np.maximum(mx, maxangle(hcor))
    return mx


def nearcut(x, steps=30, th=160.0):
    """Number of near-cut steps, plus the orbit maximum / 1000 as a tie-breaker that guides the search."""
    sig, _ = best_label(x); hcor = x * sig[..., None]; m = maxangle(hcor); cnt = (m > th).astype(float); mx = m
    for _ in range(steps):
        hcor = step04(hcor, False); m = maxangle(hcor); cnt += (m > th); mx = np.maximum(mx, m)
    return cnt + mx / 1000.0


if MODE == "4":
    g, v = climb(nearcut, haar(M), iters=200)
    print(f"(iv) worst number of steps (of 31) with corrected max angle > 160 deg: {int(v.max())} "
          f"(median {np.median(np.floor(v)):.0f}; orbit maximum at the worst star {1000 * (v.max() - np.floor(v.max())):.1f} deg)")
elif MODE == "12":
    g, v = climb(lambda x: best_label(x)[1], haar(M))
    print(f"(i) worst best-label corrected max angle found: {v.max():.1f} deg (median of the {M} climbs {np.median(v):.1f})")
    g, v = climb(growth, haar(M))
    print(f"(ii) worst one-step increase of the corrected max angle found: {v.max():+.2f} deg (median {np.median(v):+.2f})")
    sig, a0 = best_label(g); i = np.argmax(v)
    print(f"     at that star: before {a0[i]:.1f} deg")
else:
    g, v = climb(orbitmax, haar(M), iters=200)
    print(f"(iii) worst orbit maximum of the corrected max angle found: {v.max():.1f} deg (median {np.median(v):.1f}); "
          f"distance to the cut {180 - v.max():.1f} deg")
