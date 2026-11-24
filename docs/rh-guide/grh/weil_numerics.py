#!/usr/bin/env python3
"""GRH attempt, step 2c: numerical test of Weil positivity (CPU, a few minutes).

Weil's functional for L(chi, s), chi primitive mod q (here zeta: q = 1, and the odd character mod 4), on a real test
function f supported in [-a, a], h = f * f~ (f~(x) = f(-x)), F(r) = int f(x) e^{irx} dx:

  W(f) = [pole terms, zeta only] F(i/2) F(-i/2) * 2
         + h(0) log(q/pi) + (1/2pi) int |F(r)|^2 Re psi(k/2 + 1/4 + ir/2) dr      (k = 0 even, 1 odd chi)
         - sum_n Lambda(n)/sqrt(n) [chi(n) h(log n) + conj chi(n) h(-log n)]

and the explicit formula says W(f) = sum over zeros of |F(gamma)|^2 when the zeros are on the line (Weil's criterion:
GRH <=> W(f) >= 0 for all f). Part 1 checks the normalisation against the first zeros of zeta with a Gaussian.
Part 2 computes the smallest eigenvalue of W on an N-dimensional space of test functions supported in [-a, a]
(relative to the L2 norm of f) as a function of a, and checks the minimiser against the zero side.

Usage: py weil_numerics.py > weil_numerics.log
"""
import math
import time

import mpmath as mp
import numpy as np
from numpy.polynomial import legendre as L
from scipy.linalg import eigh
from scipy.special import digamma

t0 = time.time()

# ---------------------------------------------------------------- arithmetic data
NMAX = 200000
sieve = np.zeros(NMAX + 1)
spf = list(range(NMAX + 1))
for p in range(2, int(NMAX ** 0.5) + 1):
    if spf[p] == p:
        for m in range(p * p, NMAX + 1, p):
            if spf[m] == m:
                spf[m] = p
for n in range(2, NMAX + 1):
    p = spf[n]
    m = n
    while m % p == 0:
        m //= p
    if m == 1:
        sieve[n] = math.log(p)
LAMBDA = sieve


def chi4(n):
    return 0 if n % 2 == 0 else (1 if n % 4 == 1 else -1)


# ---------------------------------------------------------------- zeros of zeta
NZ = 150
ZEROS = np.array([float(mp.zetazero(k).imag) for k in range(1, NZ + 1)])
print(f"[zeros] first {NZ} zeros of zeta, gamma_1 = {ZEROS[0]:.6f}, gamma_{NZ} = {ZEROS[-1]:.3f}  ({time.time()-t0:.1f}s)")


def arch_integral(Fsq, rmax, k, npts=40001):
    r = np.linspace(-rmax, rmax, npts)
    w = np.real(digamma(k / 2 + 0.25 + 0.5j * r))
    return np.trapezoid(Fsq(r) * w, r) / (2 * math.pi)


# ---------------------------------------------------------------- part 1: calibration with a Gaussian
print("\n== Part 1: explicit formula for zeta, Gaussian g(u) = exp(-u^2/(2 s^2))")
for s in (0.25, 0.4, 0.6):
    h = lambda r: s * math.sqrt(2 * math.pi) * np.exp(-(s * r) ** 2 / 2)
    g = lambda u: np.exp(-u ** 2 / (2 * s * s))
    zero_side = 2 * np.sum(h(ZEROS))
    pole = 2 * s * math.sqrt(2 * math.pi) * math.exp(s * s / 8)
    arch = -math.log(math.pi) * g(0.0) + arch_integral(lambda r: h(r), 60.0 / s, 0)
    nmax = int(min(NMAX, math.exp(9 * s)))
    ns = np.arange(2, nmax + 1)
    prime = 2 * np.sum(LAMBDA[ns] / np.sqrt(ns) * g(np.log(ns)))
    arith = pole + arch - prime
    print(f"  s = {s:4.2f}: zero side {zero_side:.10f}   arithmetic side {arith:.10f}   diff {zero_side-arith:.2e}")


# ---------------------------------------------------------------- part 2: the quadratic form on [-a, a]
NQ = 600          # quadrature nodes on [-a, a]
NB = 10           # basis size
xq, wq = L.leggauss(NQ)


def basis_vals(t):
    """f_j(a t) = (1 - t^2)^2 P_j(t), j < NB; returns array (NB, len(t))."""
    out = np.empty((NB, len(t)))
    for j in range(NB):
        c = np.zeros(j + 1)
        c[j] = 1
        out[j] = (1 - t * t) ** 2 * L.legval(t, c)
    return out


def setup(a):
    x = a * xq
    w = a * wq
    B = basis_vals(xq)                       # (NB, NQ)
    def F(r):                                # transforms, (NB, len(r)), complex
        return (B * w) @ np.exp(1j * np.outer(x, r))
    def hconv(u):                            # h_jk(u) = int f_j(x) f_k(x - u) dx, (NB, NB)
        t2 = (x - u) / a
        inside = np.abs(t2) <= 1
        Bk = np.zeros((NB, len(x)))
        Bk[:, inside] = basis_vals(t2[inside])
        return (B * w) @ Bk.T
    return x, w, B, F, hconv


def weil_matrix(a, q, k, chi, pole):
    x, w, B, F, hconv = setup(a)
    G = hconv(0.0)                           # Gram matrix = int f_j f_k
    Wm = G * math.log(q / math.pi)
    if pole:
        Fp = (B * w) @ np.exp(-x / 2)        # F(i/2)
        Fm = (B * w) @ np.exp(x / 2)         # F(-i/2)
        Wm += np.outer(Fp, Fm) + np.outer(Fm, Fp)
    rmax = 400.0 / max(a, 0.2)
    r = np.linspace(-rmax, rmax, 60001)
    Fr = F(r)
    wt = np.real(digamma(k / 2 + 0.25 + 0.5j * r))
    Wm += np.real((Fr * wt) @ np.conj(Fr).T) * (r[1] - r[0]) / (2 * math.pi)
    nmax = int(math.exp(2 * a))
    for n in range(2, nmax + 1):
        if LAMBDA[n] == 0 or (chi and chi(n) == 0):
            continue
        c = chi(n) if chi else 1
        H = hconv(math.log(n))
        Wm -= LAMBDA[n] / math.sqrt(n) * c * (H + H.T)
    Wm = (Wm + Wm.T) / 2
    return Wm, G, F


def zero_side(F, v, zeros):
    Fz = v @ F(zeros)
    return 2 * np.sum(np.abs(Fz) ** 2)


print(f"\n== Part 2: smallest eigenvalue of W on span{{(1-t^2)^2 P_j(t)}}, j < {NB}, t = x/a  ({time.time()-t0:.1f}s)")
print("   lambda_min = min W(f) / int f^2 over the span; primes enter when 2a > log 2 (a > 0.3466)")
for name, q, k, chi, pole in (("zeta", 1, 0, None, True), ("chi_4 (odd, mod 4)", 4, 1, chi4, False)):
    print(f"\n  {name}")
    print("     a      lambda_min     lambda_2      zero side of minimiser (zeta, 150 zeros)   #prime powers")
    for a in (0.15, 0.25, 0.3466, 0.45, 0.7, 1.0, 1.5, 2.0, 2.5):
        Wm, G, F = weil_matrix(a, q, k, chi, pole)
        vals, vecs = eigh(Wm, G)
        v = vecs[:, 0]
        zs = zero_side(F, v, ZEROS) / (v @ G @ v) if name == "zeta" else float("nan")
        npp = sum(1 for n in range(2, int(math.exp(2 * a)) + 1) if LAMBDA[n] > 0)
        print(f"   {a:6.4f}  {vals[0]: .6e}  {vals[1]: .6e}   {zs: .6e}                         {npp}")


# ---------------------------------------------------------------- part 3: accuracy check where lambda_min is tiny
def weil_matrix_fine(a, q, k, chi, pole, nq, npts, rfac, nb):
    """As weil_matrix, with nq quadrature nodes, npts r-grid points on [-rfac/a, rfac/a] and nb basis functions."""
    global NB, xq, wq
    saved = (NB, xq, wq)
    NB = nb
    xq, wq = L.leggauss(nq)
    x, w, B, F, hconv = setup(a)
    G = hconv(0.0)
    Wm = G * math.log(q / math.pi)
    if pole:
        Fp = (B * w) @ np.exp(-x / 2)
        Fm = (B * w) @ np.exp(x / 2)
        Wm += np.outer(Fp, Fm) + np.outer(Fm, Fp)
    rmax = rfac / a
    r = np.linspace(-rmax, rmax, npts)
    dr = r[1] - r[0]
    acc = np.zeros((NB, NB))
    for i0 in range(0, npts, 4000):
        rc = r[i0:i0 + 4000]
        Fr = F(rc)
        wt = np.real(digamma(k / 2 + 0.25 + 0.5j * rc))
        trap = np.ones(len(rc))
        if i0 == 0:
            trap[0] = 0.5
        if i0 + 4000 >= npts:
            trap[-1] = 0.5
        acc += np.real((Fr * wt * trap) @ np.conj(Fr).T)
    Wm += acc * dr / (2 * math.pi)
    for n in range(2, int(math.exp(2 * a)) + 1):
        if LAMBDA[n] == 0 or (chi and chi(n) == 0):
            continue
        c = chi(n) if chi else 1
        H = hconv(math.log(n))
        Wm -= LAMBDA[n] / math.sqrt(n) * c * (H + H.T)
    Wm = (Wm + Wm.T) / 2
    NB, xq, wq = saved
    return Wm, G, F


print(f"\n== Part 3: zeta, accuracy check (nq nodes, npts r-points, rmax = rfac/a, nb basis functions)  ({time.time()-t0:.1f}s)")
print("     a    nb    nq    npts   rfac    lambda_min (arithmetic)   zero side of minimiser")
for a in (0.7, 1.0, 1.5):
    for nb, nq, npts, rfac in ((10, 600, 60001, 400.0), (10, 1200, 200001, 800.0), (6, 1200, 200001, 800.0)):
        Wm, G, F = weil_matrix_fine(a, 1, 0, None, True, nq, npts, rfac, nb)
        vals, vecs = eigh(Wm, G)
        v = vecs[:, 0]
        zs = zero_side(F, v, ZEROS) / (v @ G @ v)
        print(f"   {a:4.2f}  {nb:3d}  {nq:5d}  {npts:6d}  {rfac:6.0f}    {vals[0]: .6e}             {zs: .6e}")
print(f"\n[done] {time.time()-t0:.1f}s")
