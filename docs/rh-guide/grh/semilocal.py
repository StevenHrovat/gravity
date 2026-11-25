#!/usr/bin/env python3
"""Semilocal Weil test (CPU, a few minutes).

Weil's form for zeta on real test functions f supported in [-a, a], h = f * f~, F(r) = int f(x) e^{irx} dx
(same conventions as weil_numerics.py, whose normalisation was checked against the zeros to 1e-16):

  W(f) = POLE + REAL - sum over primes p, k >= 1 of log(p) p^{-k/2} [h(k log p) + h(-k log p)]
  POLE = 2 F(i/2) F(-i/2)                         (the poles of the completed zeta at s = 0, 1)
  REAL = -log(pi) h(0) + (1/2pi) int |F(r)|^2 Re psi(1/4 + ir/2) dr      (the real place, Gamma factor)

The semilocal form W_S keeps POLE, keeps REAL if 'inf' is in S, and keeps the prime terms only for primes in S.
For each S and support a it prints lambda_min = min W_S(f) / int f^2 over the span of (1 - t^2)^2 P_j(t), t = x/a,
j < nb, at two accuracy levels and two basis sizes.

Usage: py semilocal.py > semilocal.log
"""
import math
import time

import numpy as np
from numpy.polynomial import legendre as L
from scipy.linalg import eigh
from scipy.special import digamma

t0 = time.time()
PRIMES = [p for p in range(2, 200) if all(p % d for d in range(2, int(p ** 0.5) + 1))]


def basis_vals(t, nb):
    out = np.empty((nb, len(t)))
    for j in range(nb):
        c = np.zeros(j + 1)
        c[j] = 1
        out[j] = (1 - t * t) ** 2 * L.legval(t, c)
    return out


def parts(a, nb, nq, npts, rfac):
    """Gram matrix G, pole part, real-place part, and the convolution h_jk(u) for the basis on [-a, a]."""
    tq, wq = L.leggauss(nq)
    x, w = a * tq, a * wq
    B = basis_vals(tq, nb)
    Bw = B * w

    def hconv(u):
        t2 = (x - u) / a
        inside = np.abs(t2) <= 1
        Bk = np.zeros((nb, len(x)))
        Bk[:, inside] = basis_vals(t2[inside], nb)
        return Bw @ Bk.T

    G = hconv(0.0)
    Fp, Fm = Bw @ np.exp(-x / 2), Bw @ np.exp(x / 2)
    pole = np.outer(Fp, Fm) + np.outer(Fm, Fp)
    rmax = rfac / a
    r = np.linspace(-rmax, rmax, npts)
    acc = np.zeros((nb, nb))
    for i0 in range(0, npts, 4000):
        rc = r[i0:i0 + 4000]
        Fr = Bw @ np.exp(1j * np.outer(x, rc))
        wt = np.real(digamma(0.25 + 0.5j * rc))
        trap = np.ones(len(rc))
        if i0 == 0:
            trap[0] = 0.5
        if i0 + 4000 >= npts:
            trap[-1] = 0.5
        acc += np.real((Fr * wt * trap) @ np.conj(Fr).T)
    real = -math.log(math.pi) * G + acc * (r[1] - r[0]) / (2 * math.pi)
    return G, pole, real, hconv


def prime_part(a, primes, hconv, nb):
    P = np.zeros((nb, nb))
    count = 0
    for p in primes:
        k = 1
        while k * math.log(p) < 2 * a:
            H = hconv(k * math.log(p))
            P += math.log(p) * p ** (-k / 2) * (H + H.T)
            count += 1
            k += 1
    return P, count


SETS = [
    ("{inf}", True, []),
    ("{inf,2}", True, [2]),
    ("{inf,3}", True, [3]),
    ("{inf,5}", True, [5]),
    ("{inf,2,3}", True, [2, 3]),
    ("{inf,2,5}", True, [2, 5]),
    ("{inf,3,5}", True, [3, 5]),
    ("{inf,2,3,5}", True, [2, 3, 5]),
    ("{inf,2,3,5,7}", True, [2, 3, 5, 7]),
    ("all places", True, PRIMES),
    ("{2,3} no real place", False, [2, 3]),
]
AS = (0.15, 0.25, 0.3466, 0.45, 0.55, 0.7, 0.85, 1.0, 1.25, 1.5, 2.0, 2.5)
LEVELS = (("coarse", 10, 600, 60001, 400.0), ("fine", 10, 1200, 200001, 800.0), ("fine nb6", 6, 1200, 200001, 800.0))

import sys
MAIN = len(sys.argv) == 1
res = {}
for a in (AS if MAIN else ()):
    for lev, nb, nq, npts, rfac in LEVELS:
        G, pole, real, hconv = parts(a, nb, nq, npts, rfac)
        for name, with_real, primes in SETS:
            P, cnt = prime_part(a, primes, hconv, nb)
            W = pole + (real if with_real else 0) - P
            W = (W + W.T) / 2
            vals = eigh(W, G, eigvals_only=True)
            res[(name, a, lev)] = (vals[0], vals[1], cnt)
    print(f"[a = {a}] done ({time.time()-t0:.0f}s)", flush=True)

if MAIN:
    print("\nlambda_min of the semilocal form W_S on test functions supported in [-a, a] (zeta conventions)")
    print("columns: coarse (nb 10, nq 600, 60001 r-points, rmax 400/a) | fine (nb 10, nq 1200, 200001, 800/a) | fine nb 6;")
    print("[k] = number of prime powers of S with k log p < 2a. Values below ~1e-10 (nb 10) are at the noise level.")
for name, _, _ in (SETS if MAIN else ()):
    print(f"\n  S = {name}")
    print("      a     [k]      coarse          fine        fine nb6      2nd eigenvalue (fine)")
    for a in AS:
        c = res[(name, a, "coarse")]
        f = res[(name, a, "fine")]
        f6 = res[(name, a, "fine nb6")]
        print(f"   {a:6.4f}  [{f[2]:2d}]  {c[0]: .4e}  {f[0]: .4e}  {f6[0]: .4e}    {f[1]: .4e}")
if MAIN:
    print(f"\n[done] {time.time()-t0:.0f}s")


# ---------------------------------------------------------------- optional: where does lambda_min change sign?
def lam_min(a, with_real, primes, nb, nq=1200, npts=200001, rfac=800.0):
    G, pole, real, hconv = parts(a, nb, nq, npts, rfac)
    P, _ = prime_part(a, primes, hconv, nb)
    W = pole + (real if with_real else 0) - P
    return eigh((W + W.T) / 2, G, eigvals_only=True)[0]


def thresholds(first=0):
    """Bisect for the support a at which lambda_min of W_S turns negative (beyond noise), nb = 6 and nb = 10.
    `first` skips the first cases (to resume a run: --thresholds 3)."""
    print("\nThreshold a(S): first support at which lambda_min < -1e-6 (bisection, fine accuracy).")
    print("Compare with (1/2) log p*, p* = smallest prime missing from S: the point where p* enters the support of h.")
    cases = (("{inf}", [], 2), ("{inf,2}", [2], 3), ("{inf,2,3}", [2, 3], 5), ("{inf,2,3,5}", [2, 3, 5], 7),
             ("{inf,2,3,5,7}", [2, 3, 5, 7], 11), ("{inf,3}", [3], 2))
    for name, primes, pstar in cases[first:]:
        target = 0.5 * math.log(pstar)
        out = []
        for nb in (6, 10):
            lo, hi = target - 0.05, target + 0.15
            if lam_min(lo, True, primes, nb) < -1e-6 or lam_min(hi, True, primes, nb) >= -1e-6:
                out.append(f"nb {nb}: bracket failed")
                continue
            for _ in range(12):
                mid = (lo + hi) / 2
                if lam_min(mid, True, primes, nb) < -1e-6:
                    hi = mid
                else:
                    lo = mid
            out.append(f"nb {nb}: a(S) = {hi:.5f}")
        print(f"  S = {name:16s} p* = {pstar:2d}  (1/2) log p* = {target:.5f}   " + "   ".join(out), flush=True)


if __name__ == "__main__" and len(__import__("sys").argv) > 1 and __import__("sys").argv[1] == "--thresholds":
    thresholds(int(__import__("sys").argv[2]) if len(__import__("sys").argv) > 2 else 0)


# ---------------------------------------------------------------- optional: the places as symbols in the frequency gamma
def symbols():
    """Weil's form in the frequency variable r (where the zeros' imaginary parts gamma sit):
    W_S(f) = POLE + (1/2pi) int |F(r)|^2 phi_S(r) dr (full support), phi_S = sum over v in S of 2 Re (L_v'/L_v)(1/2 + ir),
    L_p = (1 - p^{-s})^{-1}, L_inf = pi^{-s/2} Gamma(s/2). For a prime, phi_p(r) = -2 log p [Re 1/(1 - p^{-1/2} e^{-i r log p}) - 1],
    a function of the phase r log p mod 2pi with mean 0 and range [-2 log p q/(1-q), 2 log p q/(1+q)], q = p^{-1/2}."""
    def phi_p(p, r):
        q = p ** -0.5
        return -2 * math.log(p) * (np.real(1 / (1 - q * np.exp(-1j * r * math.log(p)))) - 1)

    def phi_inf(r):
        return -math.log(math.pi) + np.real(digamma(0.25 + 0.5j * r))

    print("\nThe places as symbols in the frequency r (zeros at r = gamma):")
    for p in (2, 3):
        q = p ** -0.5
        print(f"  phi_{p}: period 2pi/log {p} = {2*math.pi/math.log(p):.4f}; exact range "
              f"[{-2*math.log(p)*q/(1-q):.4f}, {2*math.log(p)*q/(1+q):.4f}]; mean 0")
    for R in (1e3, 1e5, 1e6):
        r = np.linspace(0, R, int(R * 20) + 1)
        s23 = phi_p(2, r) + phi_p(3, r)
        print(f"  phi_2 + phi_3 on [0, {R:.0e}]: mean {s23.mean(): .2e}, min {s23.min(): .4f}, max {s23.max(): .4f}"
              f"  (torus range [{-2*math.log(2)*2**-0.5/(1-2**-0.5)-2*math.log(3)*3**-0.5/(1-3**-0.5):.4f}, "
              f"{2*math.log(2)*2**-0.5/(1+2**-0.5)+2*math.log(3)*3**-0.5/(1+3**-0.5):.4f}])")
    for r0 in (1.0, 14.13, 100.0, 1000.0, 1e5):
        print(f"  phi_inf({r0:g}) = {phi_inf(np.array([r0]))[0]: .4f}   (log(r/2pi) = {math.log(r0/(2*math.pi)): .4f})")


if __name__ == "__main__" and len(__import__("sys").argv) > 1 and __import__("sys").argv[1] == "--symbols":
    symbols()
