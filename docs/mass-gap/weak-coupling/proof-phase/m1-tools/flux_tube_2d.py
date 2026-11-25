# MILESTONE-1.md: the transverse problem of a thick vortex. SU(2) on an N x N box of plaquettes, boundary bonds fixed
# so that the boundary holonomy is -1 (abelian background, uniform flux a = pi/N^2 per plaquette, axis sigma_3).
# (1) Hessian of the Wilson action sum_p (1 - cos(angle U_p)) w.r.t. the interior bonds: count zero modes (expected:
#     3 per interior site, gauge) and the smallest non-zero eigenvalue (the gap), times N^2 (scale-invariant units).
# (2) Random restarts of a descent in the interior bonds: lowest action found vs the uniform abelian tube.
# Usage: python -I flux_tube_2d.py        (CPU, seconds)
import numpy as np


def qmul(a, b):
    w1, x1, y1, z1 = a; w2, x2, y2, z2 = b
    return np.array([w1*w2 - x1*x2 - y1*y2 - z1*z2, w1*x2 + x1*w2 + y1*z2 - z1*y2,
                     w1*y2 - x1*z2 + y1*w2 + z1*x2, w1*z2 + x1*y2 - y1*x2 + z1*w2])


def qinv(a):
    return a * np.array([1.0, -1, -1, -1])


def qexp(v):
    t = np.linalg.norm(v)
    return np.array([1.0, 0, 0, 0]) if t < 1e-15 else np.concatenate([[np.cos(t)], v * np.sin(t) / t])


def setup(N):
    a = np.pi / N**2
    H = {(x, y): qexp(np.array([0, 0, -y * a])) for x in range(N) for y in range(N + 1)}
    V = {(x, y): np.array([1.0, 0, 0, 0]) for x in range(N + 1) for y in range(N)}
    var = [('h', x, y) for x in range(N) for y in range(1, N)] + [('v', x, y) for x in range(1, N) for y in range(N)]
    return H, V, var


def action(N, H, V, var, vec):
    H = dict(H); V = dict(V)
    for i, (k, x, y) in enumerate(var):
        g = qexp(vec[3*i:3*i+3])
        if k == 'h':
            H[(x, y)] = qmul(g, H[(x, y)])
        else:
            V[(x, y)] = qmul(g, V[(x, y)])
    S = 0.0
    for x in range(N):
        for y in range(N):
            P = qmul(qmul(qmul(H[(x, y)], V[(x + 1, y)]), qinv(H[(x, y + 1)])), qinv(V[(x, y)]))
            S += 1.0 - np.clip(P[0], -1, 1)
    return S


for N in (3, 4, 6):
    H, V, var = setup(N)
    n = 3 * len(var); h = 1e-4
    S0 = action(N, H, V, var, np.zeros(n))
    Hs = np.zeros((n, n))
    for i in range(n):
        for j in range(i, n):
            def f(si, sj):
                v = np.zeros(n); v[i] += si * h; v[j] += sj * h
                return action(N, H, V, var, v)
            Hs[i, j] = Hs[j, i] = (f(1, 1) - f(1, -1) - f(-1, 1) + f(-1, -1)) / (4 * h * h)
    ev = np.sort(np.linalg.eigvalsh(Hs))
    nz = int(np.sum(np.abs(ev) < 1e-5)); gauge = 3 * (N - 1) ** 2
    pos = ev[np.abs(ev) >= 1e-5]
    print(f'N={N}: action of the uniform tube {S0:.6f} (N^2 * action = {N*N*S0:.4f}, pi^2/2 = {np.pi**2/2:.4f}); '
          f'dims {n}; zero modes {nz} (gauge {gauge}); negative {int(np.sum(pos < 0))}; '
          f'smallest positive {pos[pos > 0].min():.5f} (x N^2 = {pos[pos > 0].min()*N*N:.4f})')

# (2) descent from random interior starts, N = 3
rng = np.random.default_rng(1)
N = 3; H, V, var = setup(N); n = 3 * len(var)
best = []
for trial in range(12):
    v = rng.normal(size=n) * 1.5
    step = 0.2
    for it in range(1500):
        S = action(N, H, V, var, v)
        g = np.array([(action(N, H, V, var, v + 1e-6 * e) - S) / 1e-6 for e in np.eye(n)])
        v = v - step * g
    best.append(action(N, H, V, var, v))
print(f'N=3 descent from 12 random starts: lowest {min(best):.6f}, all {np.round(sorted(best), 4).tolist()}; '
      f'uniform tube {action(N, H, V, var, np.zeros(n)):.6f}')

# (3) the zero modes beyond gauge: build the gauge directions, take the rest of the null space, move along it
def adq(U, e):
    return qmul(qmul(U, np.concatenate([[0.0], e])), qinv(U))[1:]


for N in (3, 4):
    H, V, var = setup(N); n = 3 * len(var); h = 1e-4
    idx = {b: i for i, b in enumerate(var)}
    G = []
    for sx in range(1, N):
        for sy in range(1, N):
            for k in range(3):
                e = np.zeros(3); e[k] = 1.0; w = np.zeros(n)
                for b, i in idx.items():
                    kk, x, y = b
                    start = (x, y); end = (x + 1, y) if kk == 'h' else (x, y + 1)
                    Ub = H[(x, y)] if kk == 'h' else V[(x, y)]
                    if start == (sx, sy):
                        w[3*i:3*i+3] += e
                    if end == (sx, sy):
                        w[3*i:3*i+3] -= adq(Ub, e)
                G.append(w)
    G = np.array(G).T
    Hs = np.zeros((n, n))
    for i in range(n):
        for j in range(i, n):
            def f(si, sj):
                v = np.zeros(n); v[i] += si * h; v[j] += sj * h
                return action(N, H, V, var, v)
            Hs[i, j] = Hs[j, i] = (f(1, 1) - f(1, -1) - f(-1, 1) + f(-1, -1)) / (4 * h * h)
    ev, Q = np.linalg.eigh(Hs)
    null = Q[:, np.abs(ev) < 1e-5]
    Pg, _ = np.linalg.qr(G)
    rest = null - Pg @ (Pg.T @ null)
    u, s, _ = np.linalg.svd(rest, full_matrices=False)
    extra = u[:, s > 1e-3]
    S0 = action(N, H, V, var, np.zeros(n))
    print(f'N={N}: extra (non-gauge) zero modes: {extra.shape[1]}')
    for c in range(extra.shape[1]):
        w = extra[:, c]
        comp = [np.linalg.norm(w[3*i:3*i+3][[0, 1]]) for i in range(len(var))]
        vals = [action(N, H, V, var, t * w) - S0 for t in (0.05, 0.1, 0.2, 0.4)]
        print(f'  mode {c}: weight on sigma_1,2 components {np.linalg.norm(comp):.3f}; '
              f'action change at t = 0.05, 0.1, 0.2, 0.4: {np.array(vals)}')
