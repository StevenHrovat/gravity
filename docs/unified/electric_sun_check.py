#!/usr/bin/env python3
"""Electric-SU(N) round, third layer (refute-only, CPU).

Part A  thresholds and budgets (arithmetic): cstarN for N = 2, 3, 5, 11; the seam budget threeBox; the seam floor.
Part B  SU(2), 1^3 x 1 slab, exact: the pointwise twist ratio is attained at the floor e^{-2 beta}.
Part C  SU(2), 2^3 x T slab (T = 1, 2), Monte Carlo with thermodynamic integration in the twist strength:
        the pointwise (per end-face pair) twist ratio c(x, y) = K(x, Omega y)/K(x, y) and the electric factor
        rho = |1 - c|/(1 + c), for a set of end-face pairs (ordered, random, identical faces); the worst found is a lower
        bound on the boundary-uniform factor. Compared with sqrt 2 - 1.

Measurements refute only: a found rho > sqrt 2 - 1 shows that this slab is not on the pointwise electric side; nothing
here proves a bound.

Run:  python3 electric_sun_check.py [--quick]      (numpy only; seeded)
"""
import math
import sys
import time

import numpy as np

SQ2 = math.sqrt(2.0)
THETA = SQ2 - 1.0


def cstar(N):
    return (N - 1) * (2 - SQ2) / (N - 2 + SQ2)


def rhoN(N, c):
    return (N - 1) * (1 - c) / (N - 1 + c)


def three_box(theta, delta):
    return (1 + delta) * (((1 + delta) * theta * theta + delta) * theta) + delta


def part_a():
    print("== Part A: thresholds and budgets")
    for N in (2, 3, 5, 11):
        c = cstar(N)
        print(f"  N = {N:2d}: cstarN = {c:.4f}   rhoN(cstarN) = {rhoN(N, c):.4f}   (2 - sqrt 2 = {2 - SQ2:.4f})")
    for d in (0.0, 0.01, 0.02, 0.04, 0.05, 0.1):
        tb = three_box(THETA, d)
        print(f"  seam delta = {d:.2f}: threeBox = {tb:.4f}, O1 clears for mu <= {1 / tb:.2f}")
    print(f"  seam floor: delta <= e^s - 1; s = 1/50 gives {math.exp(1 / 50) - 1:.4f} (<= 1/25 = 0.04)")
    print("  SU(2) Wilson: s = 2 beta M (M seam plaquettes per layer), so beta M <= 1/100")


# ---------------------------------------------------------------------------------------------------------------------
# Quaternion helpers (unit quaternions = SU(2); tr U = 2 q0)

def qmul(a, b):
    a0, a1, a2, a3 = a[..., 0], a[..., 1], a[..., 2], a[..., 3]
    b0, b1, b2, b3 = b[..., 0], b[..., 1], b[..., 2], b[..., 3]
    return np.stack([a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3,
                     a0 * b1 + a1 * b0 + a2 * b3 - a3 * b2,
                     a0 * b2 - a1 * b3 + a2 * b0 + a3 * b1,
                     a0 * b3 + a1 * b2 - a2 * b1 + a3 * b0], axis=-1)


def qconj(a):
    return a * np.array([1.0, -1.0, -1.0, -1.0])


def haar(rng, shape):
    q = rng.normal(size=shape + (4,))
    return q / np.linalg.norm(q, axis=-1, keepdims=True)


def heatbath_x0(rng, alpha):
    """Sample x0 in [-1, 1] with density ~ sqrt(1 - x0^2) exp(alpha x0), vectorised (Creutz)."""
    out = np.empty_like(alpha)
    todo = np.arange(alpha.size)
    a = alpha.ravel()
    o = out.ravel()
    while todo.size:
        al = a[todo]
        u = rng.random(todo.size)
        small = al < 1e-8
        x0 = np.where(small, 2 * u - 1, 1.0 + np.log1p(u * np.expm1(-2 * np.maximum(al, 1e-8))) / np.maximum(al, 1e-8))
        acc = rng.random(todo.size) < np.sqrt(np.clip(1 - x0 * x0, 0, 1))
        o[todo[acc]] = x0[acc]
        todo = todo[~acc]
    return out


def heatbath(rng, W):
    """New link V with weight exp(1/2 tr(V W)) = exp(k x0), X = V What."""
    k = np.linalg.norm(W, axis=-1)
    What = W / np.maximum(k, 1e-300)[..., None]
    x0 = heatbath_x0(rng, k)
    v = rng.normal(size=W.shape[:-1] + (3,))
    v /= np.linalg.norm(v, axis=-1, keepdims=True)
    X = np.concatenate([x0[..., None], np.sqrt(np.clip(1 - x0 * x0, 0, 1))[..., None] * v], axis=-1)
    return qmul(X, qconj(What))


# ---------------------------------------------------------------------------------------------------------------------
# Slab geometry: slices t = 0..T, spatial L^3 periodic. Spatial links U[t, s, i] (t = 0 and t = T fixed: the end faces
# x and y), temporal links V[t, s] (t = 0..T-1). Plaquettes: temporal (t, s, i): U[t,s,i] V[t,s+i] U[t+1,s,i]^+ V[t,s]^+
# and interior spatial (t, s, i<j) for 0 < t < T. Boundary-slice spatial plaquettes are constants and cancel.
# The twist Omega multiplies y's k-links (k = 0) at s_k = 0 by -1: the temporal plaquettes (T-1, s, 0), s_0 = 0, flip sign.

class Slab:
    def __init__(self, L, T):
        self.L, self.T = L, T
        self.sites = [(a, b, c) for a in range(L) for b in range(L) for c in range(L)]
        self.sidx = {s: n for n, s in enumerate(self.sites)}
        self.links = {}  # name -> index; names ('U', t, s, i) / ('V', t, s)
        self.dyn = []
        for t in range(T + 1):
            for s in self.sites:
                for i in range(3):
                    self._add(('U', t, s, i), dyn=(0 < t < T))
        for t in range(T):
            for s in self.sites:
                self._add(('V', t, s), dyn=True)
        self.nl = len(self.links)
        self.plaqs = []   # list of (list of (link, dagger)), is_sheet
        for t in range(T):
            for s in self.sites:
                for i in range(3):
                    sp = self.shift(s, i)
                    p = [(('U', t, s, i), 0), (('V', t, sp), 0), (('U', t + 1, s, i), 1), (('V', t, s), 1)]
                    sheet = (t == T - 1 and i == 0 and s[0] == 0)
                    self.plaqs.append(([(self.links[n], d) for n, d in p], sheet))
        for t in range(1, T):
            for s in self.sites:
                for i in range(3):
                    for j in range(i + 1, 3):
                        si, sj = self.shift(s, i), self.shift(s, j)
                        p = [(('U', t, s, i), 0), (('U', t, si, j), 0), (('U', t, sj, i), 1), (('U', t, s, j), 1)]
                        self.plaqs.append(([(self.links[n], d) for n, d in p], False))
        self.sheet = np.array([sh for _, sh in self.plaqs])
        self.M = int(self.sheet.sum())
        # for each dynamical link: list of (plaquette index, position)
        self.touch = {l: [] for l in self.dyn}
        for pi, (p, _) in enumerate(self.plaqs):
            for pos, (l, _) in enumerate(p):
                if l in self.touch:
                    self.touch[l].append((pi, pos))

    def _add(self, name, dyn):
        self.links[name] = len(self.links)
        if dyn:
            self.dyn.append(self.links[name])

    def shift(self, s, i):
        s = list(s)
        s[i] = (s[i] + 1) % self.L
        return tuple(s)

    def plaq_value(self, Q, pi):
        p, _ = self.plaqs[pi]
        acc = None
        for l, d in p:
            q = qconj(Q[:, l]) if d else Q[:, l]
            acc = q if acc is None else qmul(acc, q)
        return acc

    def staple(self, Q, l, coef):
        W = np.zeros((Q.shape[0], 4))
        for pi, pos in self.touch[l]:
            p, _ = self.plaqs[pi]
            dag = p[pos][1]
            R = None
            for m in range(1, 4):
                l2, d2 = p[(pos + m) % 4]
                q = qconj(Q[:, l2]) if d2 else Q[:, l2]
                R = q if R is None else qmul(R, q)
            W += coef[:, pi, None] * (qconj(R) if dag else R)
        return W

    def sheet_action(self, Q):
        tot = np.zeros(Q.shape[0])
        for pi in np.nonzero(self.sheet)[0]:
            tot += 2 * self.plaq_value(Q, pi)[:, 0]
        return tot


def log_twist_ratio(slab, Qb, beta, rng, n_lambda, n_therm, n_meas):
    """log K(x, Omega y) - log K(x, y) per replica row of Qb (boundary links set, dynamical links overwritten):
    thermodynamic integration over the sheet coefficient beta (1 - 2 lambda), Gauss-Legendre in lambda."""
    R = Qb.shape[0]
    xs, ws = np.polynomial.legendre.leggauss(n_lambda)
    lams, ws = (xs + 1) / 2, ws / 2
    total = np.zeros(R)
    err2 = np.zeros(R)
    for lam, w in zip(lams, ws):
        coef = np.full((R, len(slab.plaqs)), beta)
        coef[:, slab.sheet] = beta * (1 - 2 * lam)
        Q = Qb.copy()
        Q[:, slab.dyn] = haar(rng, (R, len(slab.dyn)))
        for _ in range(n_therm):
            for l in slab.dyn:
                Q[:, l] = heatbath(rng, slab.staple(Q, l, coef))
        samples = []
        for _ in range(n_meas):
            for l in slab.dyn:
                Q[:, l] = heatbath(rng, slab.staple(Q, l, coef))
            samples.append(slab.sheet_action(Q))
        S = np.array(samples)  # (n_meas, R)
        mean = S.mean(axis=0)
        # blocked error (10 blocks)
        nb = 10
        blocks = S[: (n_meas // nb) * nb].reshape(nb, -1, R).mean(axis=1)
        se = blocks.std(axis=0, ddof=1) / math.sqrt(nb)
        total += w * (-beta * mean)
        err2 += (w * beta * se) ** 2
    return total, np.sqrt(err2)


def boundaries(slab, rng, kind, R):
    Q = np.zeros((R, slab.nl, 4))
    Q[..., 0] = 1.0
    fixed = [idx for name, idx in slab.links.items() if name[0] == 'U' and name[1] in (0, slab.T)]
    xs = [slab.links[('U', 0, s, i)] for s in slab.sites for i in range(3)]
    ys = [slab.links[('U', slab.T, s, i)] for s in slab.sites for i in range(3)]
    if kind == 'ordered':
        pass
    elif kind == 'random':
        Q[:, fixed] = haar(rng, (R, len(fixed)))
    elif kind == 'same':          # identical random end faces x = y
        h = haar(rng, (R, len(xs)))
        Q[:, xs] = h
        Q[:, ys] = h
    elif kind == 'near':          # small random fluctuation about the identity on both faces
        q = np.concatenate([np.ones((R, len(fixed), 1)), 0.15 * rng.normal(size=(R, len(fixed), 3))], axis=-1)
        Q[:, fixed] = q / np.linalg.norm(q, axis=-1, keepdims=True)
    return Q


def part_b(beta):
    print("== Part B: SU(2), 1^3 x 1 slab, exact")
    print("  one temporal link V; plaquette k: tr(x_k V y_k^+ V^+) = 2 (x_k0 y_k0 + x_k . R(V) y_k), |.| <= 2")
    print("  the twist flips y_k, so the weight changes by exp(-2 beta (x_k0 y_k0 + x_k . R y_k)) >= e^{-2 beta},")
    print("  with equality for every V when x_k, y_k are centre elements (+-1): the floor is attained.")
    c = math.exp(-2 * beta)
    print(f"  beta = {beta}: worst twist ratio = e^(-2 beta) = {c:.5f}, pointwise factor = tanh(beta) = {math.tanh(beta):.4f}"
          f"  vs sqrt 2 - 1 = {THETA:.4f}: {'REFUTES the pointwise side for this slab' if math.tanh(beta) > THETA else 'electric'}")


def part_c(beta, quick):
    print("== Part C: SU(2), 2^3 x T slab, Monte Carlo, thermodynamic integration (refute-only)")
    rng = np.random.default_rng(20261123)
    plans = [(1, 'ordered', 16), (1, 'near', 16), (1, 'same', 16), (1, 'random', 32),
             (2, 'ordered', 16), (2, 'near', 16), (2, 'same', 16), (2, 'random', 32)]
    if not quick:
        plans += [(3, 'ordered', 16), (3, 'same', 16), (4, 'ordered', 16)]
    n_lambda, n_therm, n_meas = (6, 50, 200) if quick else (8, 100, 600)
    worst = {}
    for T, kind, R in plans:
        slab = Slab(2, T)
        t0 = time.time()
        Qb = boundaries(slab, rng, kind, R)
        lr, se = log_twist_ratio(slab, Qb, beta, rng, n_lambda, n_therm, n_meas)
        c = np.exp(lr)
        cc = np.minimum(c, 1 / c)
        rho = (1 - cc) / (1 + cc)
        i = int(np.argmax(rho))
        dt = time.time() - t0
        worst.setdefault(T, []).append((rho[i], kind, lr[i], se[i]))
        print(f"  T = {T}, M = {slab.M} sheet plaquettes, {kind:7s} x {R:2d}: log c in [{lr.min():+.3f}, {lr.max():+.3f}],"
              f" worst rho = {rho[i]:.4f} (log c = {lr[i]:+.3f} +- {se[i]:.3f}), floor tanh(beta M) = "
              f"{math.tanh(beta * slab.M):.4f}   [{dt:.1f} s]")
    for T, lst in worst.items():
        r, kind, lr, se = max(lst)
        # refute at 1.645 sigma on log c: rho > theta  <=>  log c < log(elec(theta)) = log(theta) (self-dual)
        z = (math.log(THETA) - lr) / se if se > 0 else float('inf')
        verdict = "REFUTED" if abs(lr) - 1.645 * se > abs(math.log(THETA)) else "not refuted"
        print(f"  T = {T}: worst found rho = {r:.4f} ({kind}); pointwise side (rho <= {THETA:.4f}) at this slab: {verdict}"
              f" (|log c| = {abs(lr):.3f} +- {se:.3f} vs |log(sqrt2-1)| = {abs(math.log(THETA)):.3f})")


def main():
    quick = '--quick' in sys.argv
    beta = 2.3
    t0 = time.time()
    part_a()
    part_b(beta)
    part_c(beta, quick)
    print(f"== total CPU wall time {time.time() - t0:.1f} s")


if __name__ == '__main__':
    main()
