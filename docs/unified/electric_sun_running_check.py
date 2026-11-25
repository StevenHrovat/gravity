#!/usr/bin/env python3
"""Electric-SU(N) round, running outsides: refute-only CPU check.

The pointwise electric factor of a 2^3 x T SU(2) slab (beta 2.3) over *typical* end faces only: end-face pairs drawn
from the Wilson measure itself (two slices at distance T inside a thermalised 2^3 x (T + 6) slab with Haar-random outer
faces, sampled after thermalisation), instead of ordered or Haar-random faces. Same measurement as
`electric_sun_check.py` part C (thermodynamic integration in the twist strength), same code.

Reports, per T: the faces' action density (typical window), the distribution of the pointwise factor
rho = tanh(|log c|/2) over the typical pairs, the worst one, and the fraction of typical pairs on the electric side
(rho <= sqrt 2 - 1). Refute-only.

Run:  python3 electric_sun_running_check.py [--quick]
"""
import math
import sys
import time

import numpy as np

import electric_sun_check as E

THETA = E.THETA


def face_density(slab, Q, t):
    """Mean (1/2) tr of the spatial plaquettes of slice t, per replica."""
    tot = np.zeros(Q.shape[0])
    n = 0
    for s in slab.sites:
        for i in range(3):
            for j in range(i + 1, 3):
                si, sj = slab.shift(s, i), slab.shift(s, j)
                a = Q[:, slab.links[('U', t, s, i)]]
                b = Q[:, slab.links[('U', t, si, j)]]
                c = E.qconj(Q[:, slab.links[('U', t, sj, i)]])
                d = E.qconj(Q[:, slab.links[('U', t, s, j)]])
                tot += E.qmul(E.qmul(E.qmul(a, b), c), d)[:, 0]
                n += 1
    return tot / n


def thermal_faces(rng, T, R, beta, sweeps, pad=3):
    """End-face pairs from the Wilson measure: slices pad and pad + T of a thermalised 2^3 x (T + 2 pad) slab."""
    big = E.Slab(2, T + 2 * pad)
    Q = E.boundaries(big, rng, 'random', R)
    Q[:, big.dyn] = E.haar(rng, (R, len(big.dyn)))
    coef = np.full((R, len(big.plaqs)), beta)
    for _ in range(sweeps):
        for l in big.dyn:
            Q[:, l] = E.heatbath(rng, big.staple(Q, l, coef))
    small = E.Slab(2, T)
    Qs = np.zeros((R, small.nl, 4))
    Qs[..., 0] = 1.0
    for s in small.sites:
        for i in range(3):
            Qs[:, small.links[('U', 0, s, i)]] = Q[:, big.links[('U', pad, s, i)]]
            Qs[:, small.links[('U', T, s, i)]] = Q[:, big.links[('U', pad + T, s, i)]]
    return small, Qs, face_density(big, Q, pad), face_density(big, Q, pad + T)


def main():
    quick = '--quick' in sys.argv
    beta = 2.3
    rng = np.random.default_rng(20261124)
    R = 16 if quick else 64
    sweeps = 40 if quick else 150
    n_lambda, n_therm, n_meas = (6, 50, 200) if quick else (8, 100, 600)
    t_all = time.time()
    print(f"== SU(2), beta {beta}, 2^3 x T slab, typical (thermalised) end faces, {R} pairs per T")
    print(f"   faces: slices 3 and 3 + T of a 2^3 x (T + 6) slab after {sweeps} heat-bath sweeps; "
          f"TI with {n_lambda} points, {n_therm} + {n_meas} sweeps per point")
    for T in (2, 3):
        t0 = time.time()
        small, Qb, dx, dy = thermal_faces(rng, T, R, beta, sweeps)
        lr, se = E.log_twist_ratio(small, Qb, beta, rng, n_lambda, n_therm, n_meas)
        rho = np.tanh(np.abs(lr) / 2)
        order = np.sort(rho)
        frac = float(np.mean(rho <= THETA))
        # a pair counts as off the electric side if |log c| - 1.645 se > log(1 + sqrt 2)
        off = np.abs(lr) - 1.645 * se > math.log(1 + math.sqrt(2))
        i = int(np.argmax(rho))
        print(f"  T = {T}: face action density (1/2) tr P: mean {np.mean(np.r_[dx, dy]):.3f}, "
              f"range [{np.min(np.r_[dx, dy]):.3f}, {np.max(np.r_[dx, dy]):.3f}]  (ordered 1, Haar 0)")
        print(f"         log c: mean {lr.mean():+.3f}, sd over pairs {lr.std(ddof=1):.3f}, typical stat error "
              f"{np.median(se):.3f}")
        print(f"         rho over typical pairs: median {np.median(rho):.4f}, 75% {order[int(0.75 * R) - 1]:.4f}, "
              f"90% {order[int(0.9 * R) - 1]:.4f}, worst {rho[i]:.4f} (log c = {lr[i]:+.3f} +- {se[i]:.3f})")
        print(f"         fraction of typical pairs with rho <= sqrt 2 - 1 = {THETA:.4f}: {frac:.3f}; "
              f"significantly off the side (1.645 sigma, stat only): {int(off.sum())} of {R}")
        print(f"         [{time.time() - t0:.1f} s]")
    print(f"== total wall time {time.time() - t_all:.1f} s")


if __name__ == '__main__':
    main()
