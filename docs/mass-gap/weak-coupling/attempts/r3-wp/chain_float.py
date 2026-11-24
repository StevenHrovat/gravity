"""Float design run (PREREG step 1): one 2D SU(2) Wilson block (chain of n plaquettes) against the heat kernel.
High-precision floats (mpmath, 50 digits), not certified. Prints delta_n, where the sup sits, and the naive bound N_n."""
import json, mpmath as mp
mp.mp.dps = 50
J = 40  # characters j = 0, 1/2, ..., J/2 ... we index by k = 2j+1 = 1..2J+1

def dj(beta, k):            # d_j(beta) = I_{2j+1}(beta)/I_1(beta), k = 2j+1
    return mp.besseli(k, beta) / mp.besseli(1, beta)

def tune(n, t):              # d_{1/2}(beta)^n = exp(-3t/4)
    target = mp.e ** (-mp.mpf(3) * t / (4 * n))
    return mp.findroot(lambda b: dj(b, 2) - target, (mp.mpf('0.5'), mp.mpf(10) * n / t + 10), solver='anderson')

def chi(k, th):              # character of dimension k at class angle th
    s = mp.sin(th)
    if abs(s) < mp.mpf('1e-30'):
        return k if mp.cos(th) > 0 else (k if k % 2 else -k)
    return mp.sin(k * th) / s

def run(n, t, G=1500):
    t = mp.mpf(t); beta = tune(n, t)
    cr = [dj(beta, k) ** n for k in range(1, 2 * J + 2)]
    ck = [mp.e ** (-t * ((k * k - 1) / mp.mpf(4))) for k in range(1, 2 * J + 2)]
    best = (mp.mpf(0), 0); absmax = mp.mpf(0); kmin = mp.inf
    rows = []
    for i in range(G + 1):
        th = mp.pi * i / G
        ch = [chi(k, th) for k in range(1, 2 * J + 2)]
        r = sum(k * c * x for k, c, x in zip(range(1, 2 * J + 2), cr, ch))
        K = sum(k * c * x for k, c, x in zip(range(1, 2 * J + 2), ck, ch))
        f = mp.log(r) - mp.log(K)
        if abs(f) > best[0]: best = (abs(f), th)
        absmax = max(absmax, abs(r - K)); kmin = min(kmin, K)
        if i % (G // 6) == 0: rows.append((float(th), float(f)))
    return dict(n=n, t=float(t), beta=float(beta), delta=float(best[0]), theta_at_sup=float(best[1]),
                naive=float(absmax / kmin), Kmin=float(kmin), profile=rows)

if __name__ == '__main__':
    out = []
    for t in (1, 0.5):
        for l in (1, 2, 4, 8):
            r = run(l * l, t); out.append(r)
            print(f"t={r['t']} l={l} n={r['n']} beta={r['beta']:.4f} delta={r['delta']:.3e} at th={r['theta_at_sup']:.3f}"
                  f" n*delta={r['n']*r['delta']:.3f} naive={r['naive']:.3e} Kmin={r['Kmin']:.3e}")
            print('   profile', [(round(a, 3), f'{b:.2e}') for a, b in r['profile']])
    json.dump(out, open('chain_float.json', 'w'), indent=1)
