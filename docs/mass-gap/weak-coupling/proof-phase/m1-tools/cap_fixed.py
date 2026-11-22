# Strong cap invariance test (NT-B.md 3): stars with all elements in the fixed cap C(u, r) = {x : <x,u> >= cos r}; is
# every image element t_c (Balaban's star map, L = 13, d = 4, trivial shell) again in C(u, r)? Reports the largest
# excess angle(t_c, u) - r over random stars (uniform in the cap, and concentrated on its boundary) and a local search.
import sys, os
import numpy as np
sys.argv = sys.argv[:1] + ["1", "0", "13", "4"]
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "star_dynamics.py"), encoding="utf-8").read()
ns = {}; exec(compile(src.split("for zlift in (False, True):")[0], "star_dynamics.py", "exec"), ns)
qmul, qexp, step04, n = ns["qmul"], ns["qexp"], ns["step"], ns["n"]
rng = np.random.default_rng(23)
u = np.array([1.0, 0, 0, 0])


def in_cap(m, r, boundary=False):
    v = rng.normal(size=(m, n, 3)); v /= np.linalg.norm(v, axis=-1, keepdims=True)
    ang = np.full((m, n), r) if boundary else r * rng.random((m, n)) ** (1 / 3)
    return qexp(v * ang[..., None])                      # points at angle <= r from u = identity


def excess(g, r):
    t = step04(g, False)
    return np.degrees(np.arccos(np.clip(t[..., 0], -1, 1))).max(1) - np.degrees(r)


for rdeg in (30, 60, 80, 84.4, 89):
    r = np.radians(rdeg)
    e1 = excess(in_cap(20000, r), r).max(); e2 = excess(in_cap(20000, r, True), r).max()
    g = in_cap(300, r, True); val = excess(g, r); s = np.full(300, 0.2)
    for _ in range(150):
        cand = qmul(qexp(s[:, None, None] * rng.normal(size=g.shape[:-1] + (3,))), g)
        ang = np.degrees(np.arccos(np.clip(cand[..., 0], -1, 1))).max(1)
        v = np.where(ang <= rdeg + 1e-9, excess(cand, r), -1e9); b = v >= val
        g[b] = cand[b]; val[b] = v[b]; s = np.where(b, s * 1.1, s * 0.8).clip(1e-6, 1)
    print(f"cap radius {rdeg:5.1f} deg: largest excess of an image element: uniform {e1:+.4f}, boundary {e2:+.4f}, "
          f"local search {val.max():+.4f} deg")
