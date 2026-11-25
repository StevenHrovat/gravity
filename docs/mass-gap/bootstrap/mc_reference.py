"""Monte Carlo reference values for the bootstrap, in any dimension d (CPU only).

- SU(2), Wilson action S = beta sum_p (1 - (1/2) tr U_p), periodic L^d lattice, Kennedy-Pendleton heat bath + overrelaxation on a
  checkerboard (same algorithm as lattice/su2.py, rewritten for general d).
- Measures the plaquette and the rectangular Wilson loops W(R,T) (averaged over all planes and sites), and arbitrary loops given as
  step tuples (used by check_equations.py).

Usage (from docs/mass-gap/):
    py bootstrap/mc_reference.py            # the pre-registered reference runs, written to results/bootstrap_mc_reference.json
"""

import os
os.environ['CUDA_VISIBLE_DEVICES'] = '-1'  # never touch the GPU (it runs other jobs); set before any other import


import json
import os
import sys
import time

import numpy as np


def qmul(a, b):
    a0, a1, a2, a3 = a[..., 0], a[..., 1], a[..., 2], a[..., 3]
    b0, b1, b2, b3 = b[..., 0], b[..., 1], b[..., 2], b[..., 3]
    out = np.empty(np.broadcast_shapes(a.shape, b.shape))
    out[..., 0] = a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3
    out[..., 1] = a0 * b1 + b0 * a1 - (a2 * b3 - a3 * b2)
    out[..., 2] = a0 * b2 + b0 * a2 - (a3 * b1 - a1 * b3)
    out[..., 3] = a0 * b3 + b0 * a3 - (a1 * b2 - a2 * b1)
    return out


def qdag(a):
    out = -a.copy()
    out[..., 0] = a[..., 0]
    return out


def qnorm(a):
    return np.sqrt(np.sum(a * a, axis=-1))


class LatticeD:
    def __init__(self, d, L, beta, seed):
        self.d, self.L, self.beta = d, L, beta
        self.shape = (L,) * d
        self.rng = np.random.default_rng(seed)
        self.U = np.zeros((d,) + self.shape + (4,))
        self.U[..., 0] = 1.0
        idx = np.indices(self.shape).sum(axis=0)
        self.parity = [(idx % 2) == p for p in (0, 1)]

    def sh(self, x, mu, s):
        return np.roll(x, -s, axis=mu)

    def staple(self, mu):
        U = self.U
        A = np.zeros(self.shape + (4,))
        for nu in range(self.d):
            if nu == mu:
                continue
            A += qmul(qmul(self.sh(U[nu], mu, 1), qdag(self.sh(U[mu], nu, 1))), qdag(U[nu]))
            Unu_m = self.sh(U[nu], nu, -1)
            A += qmul(qmul(qdag(self.sh(Unu_m, mu, 1)), qdag(self.sh(U[mu], nu, -1))), Unu_m)
        return A

    def _kp_x0(self, alpha):
        rng = self.rng
        n = alpha.shape[0]
        x0 = np.empty(n)
        todo = np.arange(n)
        while todo.size:
            a = alpha[todo]
            r1 = 1.0 - rng.random(todo.size)
            r2 = rng.random(todo.size)
            r3 = 1.0 - rng.random(todo.size)
            r4 = rng.random(todo.size)
            lam2 = -(np.log(r1) + np.cos(2 * np.pi * r2) ** 2 * np.log(r3)) / (2 * a)
            ok = r4 * r4 <= 1.0 - lam2
            x0[todo[ok]] = 1.0 - 2.0 * lam2[ok]
            todo = todo[~ok]
        return x0

    def heatbath(self):
        for mu in range(self.d):
            for p in (0, 1):
                m = self.parity[p]
                A = self.staple(mu)[m]
                k = qnorm(A)
                Ahat = A / k[:, None]
                x0 = self._kp_x0(self.beta * k)
                v = self.rng.normal(size=(x0.size, 3))
                v /= np.linalg.norm(v, axis=1)[:, None]
                X = np.empty((x0.size, 4))
                X[:, 0] = x0
                X[:, 1:] = v * np.sqrt(np.maximum(0.0, 1.0 - x0 * x0))[:, None]
                Um = self.U[mu]
                Um[m] = qmul(X, qdag(Ahat))

    def overrelax(self):
        for mu in range(self.d):
            for p in (0, 1):
                m = self.parity[p]
                A = self.staple(mu)[m]
                Ad = qdag(A / qnorm(A)[:, None])
                Um = self.U[mu]
                Um[m] = qmul(qmul(Ad, qdag(Um[m])), Ad)

    def reunitarise(self):
        self.U /= qnorm(self.U)[..., None]

    def loop(self, path):
        """Site average of (1/2) tr of the closed path (steps +-a, a = 1..d) started at every site."""
        off = [0] * self.d
        P = None
        for s in path:
            a = abs(s) - 1
            if s > 0:
                F = self.U[a]
                o = list(off)
            else:
                o = list(off)
                o[a] -= 1
                F = None
            G = self.U[a]
            G = np.roll(G, shift=tuple(-c for c in o), axis=tuple(range(self.d)))
            if s < 0:
                G = qdag(G)
            P = G if P is None else qmul(P, G)
            off[a] += 1 if s > 0 else -1
        assert all(c == 0 for c in off), 'path not closed'
        if P is None:
            return 1.0
        return float(P[..., 0].mean())

    def plaquette(self):
        s, n = 0.0, 0
        for a in range(1, self.d + 1):
            for b in range(a + 1, self.d + 1):
                s += self.loop((a, b, -a, -b))
                n += 1
        return s / n

    def wilson(self, R, T):
        s, n = 0.0, 0
        for a in range(1, self.d + 1):
            for b in range(1, self.d + 1):
                if a == b:
                    continue
                s += self.loop((a,) * R + (b,) * T + (-a,) * R + (-b,) * T)
                n += 1
        return s / n


def run(d, L, beta, seed, n_therm, n_meas, every, loops_RT, extra_paths=(), log=None):
    lat = LatticeD(d, L, beta, seed)
    t0 = time.time()
    for i in range(n_therm):
        lat.heatbath()
        for _ in range(3):
            lat.overrelax()
        if i % 20 == 0:
            lat.reunitarise()
    data = {'plaq': [], 'W': {f'{R}x{T}': [] for R, T in loops_RT}, 'extra': [[] for _ in extra_paths]}
    for m in range(n_meas):
        for _ in range(every):
            lat.heatbath()
            for _ in range(3):
                lat.overrelax()
        lat.reunitarise()
        data['plaq'].append(lat.plaquette())
        for R, T in loops_RT:
            data['W'][f'{R}x{T}'].append(lat.wilson(R, T))
        for k, p in enumerate(extra_paths):
            data['extra'][k].append(lat.loop(p))
        if log and m % 100 == 0:
            print(f'd={d} L={L} beta={beta} meas {m}/{n_meas} plaq {np.mean(data["plaq"]):.5f} t={time.time()-t0:.0f}s', file=log, flush=True)
    data['seconds'] = time.time() - t0
    return data


def binned(x, nb=20):
    x = np.asarray(x)
    n = len(x) // nb * nb
    b = x[:n].reshape(nb, -1).mean(1)
    return float(x.mean()), float(b.std(ddof=1) / np.sqrt(nb))


def creutz_jack(W11, W12, W22, nb=20):
    a = [np.asarray(v) for v in (W11, W12, W22)]
    n = len(a[0]) // nb * nb
    bins = [v[:n].reshape(nb, -1).mean(1) for v in a]
    tot = [v[:n].mean() for v in a]
    f = lambda w11, w12, w22: -np.log(w22 * w11 / w12 ** 2)
    est = f(*tot)
    jk = []
    for i in range(nb):
        m = [(t * nb - b[i]) / (nb - 1) for t, b in zip(tot, bins)]
        jk.append(f(*m))
    jk = np.array(jk)
    err = np.sqrt((nb - 1) / nb * ((jk - jk.mean()) ** 2).sum())
    return float(est), float(err)


def _job(args):
    d, L, beta, seed, n_therm, n_meas, every = args
    os.environ.setdefault('OMP_NUM_THREADS', '1')
    RT = [(1, 1), (1, 2), (2, 2), (1, 3), (2, 3), (3, 3)]
    with open(os.path.join(os.path.dirname(__file__), f'mc_ref_d{d}_b{beta}_L{L}.log'), 'w') as log:
        data = run(d, L, beta, seed, n_therm, n_meas, every, RT, log=log)
    out = dict(d=d, L=L, beta=beta, seed=seed, n_therm=n_therm, n_meas=n_meas, every=every, seconds=data['seconds'],
               plaquette=binned(data['plaq']))
    out['W'] = {k: binned(v) for k, v in data['W'].items()}
    out['chi2'] = creutz_jack(data['W']['1x1'], data['W']['1x2'], data['W']['2x2'])
    return out


if __name__ == '__main__':
    from multiprocessing import Pool
    jobs = [
        (4, 8, 2.0, 11, 200, 1000, 2),
        (4, 10, 2.0, 12, 200, 1000, 2),
        (4, 12, 2.3, 13, 300, 1000, 2),
        (4, 14, 2.4, 14, 300, 800, 2),
        (2, 64, 2.0, 15, 200, 2000, 1),
    ]
    with Pool(len(jobs)) as pool:
        res = pool.map(_job, jobs)
    path = os.path.join(os.path.dirname(__file__), '..', 'results', 'bootstrap_mc_reference.json')
    with open(path, 'w') as f:
        json.dump(dict(note='CPU Monte Carlo reference values for the bootstrap (mc_reference.py); errors from 20 bins; chi2 jackknife',
                       runs=res), f, indent=1)
    for r in res:
        print(r['d'], r['L'], r['beta'], r['plaquette'], r['W']['1x2'], r['W']['2x2'], r['chi2'], f"{r['seconds']:.0f}s")
