# NT'(b') tests (NT-B.md). Questions fixed before running:
#  M  measure formula used in the proof of NT'(a): P(|<x,u>| < s) for u uniform on S^3 equals (2/pi)(s sqrt(1-s^2) + arcsin s).
#  B1 long orbits: labels chosen at the root by the best-cap rule (sign pattern whose corrected star has the smallest
#     enclosing cap); count steps with a corrected relative angle above 160 deg and above 168.7 deg over 300 steps.
#  B2 cap invariance (candidate route to (b')): is the enclosing-cap radius of the corrected star non-increasing along the
#     orbit? If so, every corrected relative angle stays <= 2 * (root cap radius) <= 168.7 deg for ever (by NT'(a)).
#     Worst increase from random stars and from an adversarial search.
# Cap radius: cos r = |p|, p the minimum-norm point of the convex hull of the corrected star (duality), computed by
# accelerated projected gradient on the simplex (batched; no SciPy needed).
# Usage: python -I nt_b.py [stars] [steps] [adversarial starts] [iterations]
import sys, os, itertools
import numpy as np

NS = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
T = int(sys.argv[2]) if len(sys.argv) > 2 else 300
NA = int(sys.argv[3]) if len(sys.argv) > 3 else 60
IT = int(sys.argv[4]) if len(sys.argv) > 4 else 80
sys.argv = sys.argv[:1] + ["1", "0", "13", "4"]
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "star_dynamics.py"), encoding="utf-8").read()
ns = {}; exec(compile(src.split("for zlift in (False, True):")[0], "star_dynamics.py", "exec"), ns)
qmul, qinv, qexp, step04, n = ns["qmul"], ns["qinv"], ns["qexp"], ns["step"], ns["n"]
rng = np.random.default_rng(17)
SIGNS = np.array([(1,) + s for s in itertools.product((1, -1), repeat=n - 1)], float)
BIG = 1e3


def proj_simplex(v):
    """Euclidean projection of each row of v onto the probability simplex."""
    m = v.shape[-1]
    u = -np.sort(-v, axis=-1); css = np.cumsum(u, axis=-1) - 1
    ind = np.arange(1, m + 1)
    cond = u - css / ind > 0
    rho = m - np.argmax(cond[..., ::-1], axis=-1) - 1
    theta = np.take_along_axis(css, rho[..., None], -1) / (rho[..., None] + 1)
    return np.maximum(v - theta, 0)


def cap_cos(x, iters=1500):
    """x: (..., n, 4) points; returns cos of the enclosing-cap radius = |min-norm point of the convex hull| (0 if the
    origin is in the hull)."""
    G = x @ np.swapaxes(x, -1, -2)                       # Gram matrices
    m = x.shape[-2]
    lam = np.full(x.shape[:-1], 1.0 / m); y = lam.copy(); tk = 1.0
    step = 1.0 / (2 * m)
    for _ in range(iters):
        grad = 2 * np.einsum("...ij,...j->...i", G, y)
        new = proj_simplex(y - step * grad)
        tn = (1 + np.sqrt(1 + 4 * tk * tk)) / 2
        y = new + ((tk - 1) / tn) * (new - lam)
        lam, tk = new, tn
    p = np.einsum("...i,...ij->...j", lam, x)
    return np.linalg.norm(p, axis=-1)


def best_cap_label(x):
    """x: (m, n, 4). Best of the 128 sign patterns (mod global sign) by enclosing-cap radius."""
    cand = x[:, None, :, :] * SIGNS[None, :, :, None]   # (m, 128, n, 4)
    c = cap_cos(cand, iters=400)
    k = np.argmax(c, axis=1)
    lab = SIGNS[k]
    return lab, cap_cos(x * lab[..., None])


def maxangle(g):
    rel = qmul(g[:, :, None, :], qinv(g[:, None, :, :]))
    return np.degrees(np.arccos(np.clip(rel[..., 0], -1, 1))).max((1, 2))


def haar(m):
    g = rng.normal(size=(m, n, 4)); return g / np.linalg.norm(g, axis=-1, keepdims=True)


# ---------- M ----------
u = rng.normal(size=(2_000_000, 4)); u /= np.linalg.norm(u, axis=1, keepdims=True)
for s in (0.05, 0.0983, 0.2, 0.5):
    emp = np.mean(np.abs(u[:, 0]) < s); th = (2 / np.pi) * (s * np.sqrt(1 - s * s) + np.arcsin(s))
    print(f"M  s={s}: Monte Carlo {emp:.5f}  formula {th:.5f}")


def run_orbits(g, steps, track_cap=True):
    m = g.shape[0]
    lab, c0 = best_cap_label(g)
    h = g * lab[..., None]
    r0 = np.degrees(np.arccos(np.clip(c0, -1, 1)))
    above160 = np.zeros(m, int); above1687 = np.zeros(m, int); maxa = maxangle(h); worst_inc = np.full(m, -1e9)
    rprev = r0.copy()
    for t in range(steps):
        h = step04(h, False)
        a = maxangle(h); maxa = np.maximum(maxa, a)
        above160 += a > 160; above1687 += a > 168.7
        if track_cap and t < 60:                               # the orbit has contracted long before step 60
            r = np.degrees(np.arccos(np.clip(cap_cos(h), -1, 1)))
            worst_inc = np.maximum(worst_inc, r - rprev); rprev = r
    return r0, maxa, above160, above1687, worst_inc


g = haar(NS)
r0, maxa, a160, a1687, inc = run_orbits(g, T)
print(f"B1 Haar stars ({NS}), {T} steps: root cap radius max {r0.max():.1f} deg (bound 84.4); orbit max angle max "
      f"{maxa.max():.1f}; steps above 160: total {a160.sum()}, max per orbit {a160.max()}; above 168.7: {a1687.sum()}")
print(f"B2 cap radius along orbits (first 60 steps): largest one-step increase {inc.max():+.3f} deg")


# ---------- adversarial: maximise the cap-radius increase over 60 steps (plus near-cut steps) ----------
def objective(G):
    r0, maxa, a160, a1687, inc = run_orbits(G, 60)
    return inc + 0.01 * maxa, a160, maxa


G = haar(NA); val, a160, mx = objective(G); s = np.full(NA, 0.3)
for it in range(IT):
    cand = qmul(qexp(s[:, None, None] * rng.normal(size=G.shape[:-1] + (3,))), G)
    v, c160, cmx = objective(cand); b = v >= val
    G[b] = cand[b]; val[b] = v[b]; a160[b] = c160[b]; mx[b] = cmx[b]; s = np.where(b, s * 1.1, s * 0.8).clip(1e-6, 1)
    if it % 20 == 0 or it == IT - 1:
        print(f"  adversarial it {it}: largest cap-radius increase {(val - 0.01 * mx).max():+.3f} deg; "
              f"orbit max angle {mx.max():.1f}; steps above 160 (max per orbit) {a160.max()}")
