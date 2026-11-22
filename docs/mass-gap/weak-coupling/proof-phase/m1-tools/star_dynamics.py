# D-pin scoping, numerical side check (CPU, seconds). Pre-registered question (D-PIN.md section 2.3):
#   Under the star map of a block centre with a trivial shell, which deep stars stay deep?  Expectation: generic deep
#   stars become moderate in one step (the 2d rows of weights are almost equal), and only stars at or near patterns
#   where the average jumps (centre-valued patterns) persist.
# Star map (NOTE.md 2.2, Balaban [I] (0.4) with a trivial shell): t_c = exp(sum_b F(c,b) log(g_b g_c^-1)) g_c,
#   F(c,b) = q + e1 [b = c] - e2 [b = -c], principal log on SU(2) with log(-1) := 0.
# Variant "zlift": the same with every relative element first moved into the half-sphere of the reference
#   (g_b g_c^-1 -> -g_b g_c^-1 if its real part is < 0) and the sign put back by weighted majority (D-PIN.md 2.2, P0).
# Usage: python -I star_dynamics.py [samples] [steps] [L] [d]
import sys
import numpy as np

S = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
T = int(sys.argv[2]) if len(sys.argv) > 2 else 12
L = int(sys.argv[3]) if len(sys.argv) > 3 else 13
d = int(sys.argv[4]) if len(sys.argv) > 4 else 4
rng = np.random.default_rng(20261122)
n = 2 * d
e1 = (L + 1) / (2 * L ** d); e2 = (L - 1) / (2 * L ** d); q = (1 - L ** (-d)) / (2 * d)
opp = [b ^ 1 for b in range(n)]                     # directions ordered +mu, -mu
F = np.full((n, n), q)
for c in range(n):
    F[c, c] += e1; F[c, opp[c]] -= e2


def qmul(a, b):
    w1, x1, y1, z1 = np.moveaxis(a, -1, 0); w2, x2, y2, z2 = np.moveaxis(b, -1, 0)
    return np.stack([w1*w2 - x1*x2 - y1*y2 - z1*z2, w1*x2 + x1*w2 + y1*z2 - z1*y2,
                     w1*y2 - x1*z2 + y1*w2 + z1*x2, w1*z2 + x1*y2 - y1*x2 + z1*w2], -1)


def qinv(a):
    return a * np.array([1, -1, -1, -1])


def qlog(a):                                          # principal log, 3-vector, log(-1) := 0
    w = np.clip(a[..., 0], -1, 1); v = a[..., 1:]
    th = np.arccos(w); s = np.linalg.norm(v, axis=-1)
    fac = np.where(s > 1e-12, th / np.maximum(s, 1e-300), 1.0)
    out = v * fac[..., None]
    return np.where((th > np.pi - 1e-12)[..., None], 0.0, out)


def qexp(v):
    th = np.linalg.norm(v, axis=-1); s = np.where(th > 1e-12, np.sin(th) / np.maximum(th, 1e-300), 1.0)
    return np.concatenate([np.cos(th)[..., None], v * s[..., None]], -1)


def step(g, zlift):
    t = np.empty_like(g)
    for c in range(n):
        rel = qmul(g, qinv(g[:, c:c+1, :]))           # g_b g_c^-1, shape (S, n, 4)
        if zlift:
            sgn = np.where(rel[..., 0] < 0, -1.0, 1.0)
            rel = rel * sgn[..., None]
            maj = np.where((sgn * F[c][None, :]).sum(1) < 0, -1.0, 1.0)
        a = (F[c][None, :, None] * qlog(rel)).sum(1)
        tc = qmul(qexp(a), g[:, c, :])
        if zlift:
            tc = tc * maj[:, None]
        t[:, c, :] = tc
    return t


def spreads(g):
    th = []
    for b in range(n):
        rel = qmul(g, qinv(g[:, b:b+1, :]))
        th.append(np.arccos(np.clip(rel[..., 0], -1, 1)))
    th = np.stack(th, 1)                               # (S, n, n) angles in [0, pi]
    s = th.max((1, 2)); sz = np.minimum(th, np.pi - th).max((1, 2))
    return s, sz


for zlift in (False, True):
    g = rng.normal(size=(S, n, 4)); g /= np.linalg.norm(g, axis=-1, keepdims=True)   # Haar stars
    print(f"--- {'zlift' if zlift else 'Balaban (0.4)'}  L={L} d={d} samples={S}")
    for k in range(T + 1):
        s, sz = spreads(g)
        if k in (0, 1, 2, 3, 6, T):
            print(f"step {k:2d}: spread>0.5: {np.mean(s > 0.5):.4f}   spread>0.05: {np.mean(s > 0.05):.4f}   "
                  f"deep & centre-valued (dist to centre<0.05, spread>0.5): {np.mean((s > 0.5) & (sz < 0.05)):.4f}   "
                  f"max spread {s.max():.3f}")
        g = step(g, zlift)
