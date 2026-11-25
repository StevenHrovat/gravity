#!/usr/bin/env python3
"""Scale-by-scale positivity of Weil's form as a Szego (Levinson) recursion (CPU, a few minutes).

Weil's form restricted to a grid of translated cells is a Toeplitz matrix: the cells are translates of one another by
eps and the form is translation invariant. Cell of order r: b = 1_[0,eps] convolved r times (r = 1: step functions;
r = 2, 3: C^0, C^1 splines). Then h_jk = b * b~ (shifted by (j-k) eps) is the centred cardinal B-spline of order 2r,
and the entries are the explicit-formula functional E applied to it:

  t_m = E(e_m),  e_m(u) = (B(u - m eps) + B(u + m eps)) / 2,   B(u) = eps^{2r-1} B_{2r}(u/eps + r),
  E(h) = POLE + REAL - sum_n Lambda(n) n^{-1/2} [h(log n) + h(-log n)]        (h even)
  POLE = int h(u) 2 cosh(u/2) du
  REAL = -(log pi + gamma) h(0) + int_0^inf [e^{-2u} h(0) - e^{-u/2} h(u)] 2 / (1 - e^{-2u}) du

These are the conventions of weil_numerics.py and semilocal.py (POLE = 2 F(i/2) F(-i/2); REAL is the same Gamma-factor
term written in the u variable). Part 0 checks E against the zeros. A function on [-a, a] made of N cells has
2a = (N - 1 + r) eps; the Toeplitz section T_N is positive definite iff all reflection coefficients k_1..k_{N-1} lie in
(-1, 1) (Szego recursion, Levinson-Durbin). The prediction error E_N = t_0 prod (1 - k_j^2) is the margin the newest
cell adds. A prime power n enters the entries t_m with |log n - m eps| < r eps: the corner of the section, the boundary.

Usage: py induction.py > induction.log
"""
import time
from math import comb, factorial

import mpmath as mp

mp.mp.dps = 60
t0 = time.time()


def vm_list(nmax):
    """(n, Lambda(n)) for prime powers n <= nmax."""
    out = []
    for n in range(2, nmax + 1):
        p = next(d for d in range(2, n + 1) if n % d == 0)
        m = n
        while m % p == 0:
            m //= p
        if m == 1:
            out.append((n, mp.log(p)))
    return out


def is_pow(n, p):
    while n % p == 0:
        n //= p
    return n == 1


# ------------------------------------------------------------------------------------------------ part 0: check E
def E_general(h, hsupp, primes_vm, knots=()):
    """E(h) for an even h supported in [-hsupp, hsupp] (quadrature, split at the given positive knots)."""
    pts = sorted(set([mp.mpf(0)] + [mp.mpf(k) for k in knots if 0 < k < hsupp] + [mp.mpf(hsupp)]))
    pole = 2 * mp.quad(lambda u: h(u) * 2 * mp.cosh(u / 2), pts)
    h0 = h(0)
    real = -(mp.log(mp.pi) + mp.euler) * h0 + mp.quad(
        lambda u: (mp.exp(-2 * u) * h0 - mp.exp(-u / 2) * h(u)) * 2 / (1 - mp.exp(-2 * u)), pts)
    if h0 != 0:
        real += -h0 * mp.log(1 - mp.exp(-2 * pts[-1]))   # int_L^inf h0 e^{-2u} 2/(1 - e^{-2u}) du
    prime = -2 * sum(lam / mp.sqrt(n) * h(mp.log(n)) for n, lam in primes_vm if mp.log(n) < hsupp)
    return pole + real + prime


def check_against_zeros():
    print("Part 0. Check of the functional E against the zeros: E(h) = sum over zeros of h^(gamma).")
    vm = vm_list(10 ** 4)
    zeros = [mp.im(mp.zetazero(j)) for j in range(1, 61)]
    for s in (mp.mpf("0.2"), mp.mpf("0.12")):
        h = lambda u, s=s: mp.exp(-u * u / (2 * s * s))
        arith = E_general(h, 40 * s, vm, knots=(1,))
        zs = 2 * sum(s * mp.sqrt(2 * mp.pi) * mp.exp(-s * s * g * g / 2) for g in zeros)  # +-gamma
        print(f"  Gaussian, width {mp.nstr(s, 3)}: arithmetic side {mp.nstr(arith, 18)}, zero side (60 zeros) "
              f"{mp.nstr(zs, 18)}, difference {mp.nstr(arith - zs, 3)}")
    print(f"  [{time.time()-t0:.0f}s]", flush=True)


# ------------------------------------------------------------------------------------------- the Toeplitz entries
class Grid:
    def __init__(self, eps, r):
        self.eps, self.r, self.k = mp.mpf(eps), r, 2 * r
        self.poleC = (4 * mp.sinh(self.eps / 4)) ** (2 * r)    # int B(u) e^{u/2} du

    def B(self, u):
        """eps^{2r-1} B_{2r}(u/eps + r): the centred B-spline of order 2r, support [-r eps, r eps]."""
        x = u / self.eps + self.r
        if x <= 0 or x >= self.k:
            return mp.mpf(0)
        k = self.k
        s = sum((-1) ** j * comb(k, j) * (x - j) ** (k - 1) for j in range(k + 1) if x - j > 0)
        return self.eps ** (k - 1) * s / factorial(k - 1)

    def e(self, m, u):
        c = m * self.eps
        return (self.B(u - c) + self.B(u + c)) / 2

    def length(self, N):
        """support length 2a of a combination of N cells"""
        return (N - 1 + self.r) * self.eps

    def smooth(self, M):
        out = []
        for m in range(M + 1):
            c = m * self.eps
            pole = self.poleC * 2 * mp.cosh(c / 2)
            h0 = self.e(m, 0)
            lo = max(mp.mpf(0), c - self.r * self.eps)
            hi = c + self.r * self.eps
            knots = sorted(set([mp.mpf(0)] + [c + j * self.eps for j in range(-self.r, self.r + 1)
                                               if c + j * self.eps > 0] + [hi]))
            f = lambda u: (mp.exp(-2 * u) * h0 - mp.exp(-u / 2) * self.e(m, u)) * 2 / (1 - mp.exp(-2 * u))
            if h0 == 0:
                knots = [x for x in knots if x >= lo]
            real = -(mp.log(mp.pi) + mp.euler) * h0 + mp.quad(f, knots)
            if h0 != 0:
                real += -h0 * mp.log(1 - mp.exp(-2 * hi))
            out.append(pole + real)
        return out

    def prime(self, M, vm, keep=lambda n: True):
        out = []
        for m in range(M + 1):
            pr = mp.mpf(0)
            for n, lam in vm:
                if keep(n):
                    L = mp.log(n)
                    pr -= lam / mp.sqrt(n) * (self.e(m, L) + self.e(m, -L))
            out.append(pr)
        return out


def levinson(t):
    """Reflection coefficients k_1..k_M and prediction errors E_0..E_M of a real symmetric Toeplitz sequence t;
    stops at the first |k| >= 1 (that k is the last entry of the returned list)."""
    E, a, ks = [t[0]], [], []
    for n in range(1, len(t)):
        acc = t[n] + sum(a[j] * t[n - 1 - j] for j in range(n - 1))
        k = -acc / E[-1]
        ks.append(k)
        if abs(k) >= 1:
            break
        a = [a[j] + k * a[n - 2 - j] for j in range(n - 1)] + [k]
        E.append(E[-1] * (1 - k * k))
    return ks, E


def min_eig(t, N):
    """smallest eigenvalue of the N x N section, relative to t_0"""
    T = mp.matrix(N, N)
    for i in range(N):
        for j in range(N):
            T[i, j] = t[abs(i - j)]
    ev = mp.eigsy(T, eigvals_only=True)
    return min(ev) / t[0]


# ------------------------------------------------------------------------------------------------ part 1: the run
def run(eps, r, amax, show_table=True):
    g = Grid(eps, r)
    M = int(mp.floor(2 * amax / g.eps)) - r + 1
    vm = vm_list(int(mp.exp(g.length(M + 1))) + 2)
    sm = g.smooth(M)
    pr = g.prime(M, vm)
    t = [sm[m] + pr[m] for m in range(M + 1)]
    ks, E = levinson(t)
    print(f"\nPart 1. Full form, cells of order r = {r} (h = B-spline of order {2*r}), grid eps = {eps}, "
          f"sections up to N = {M + 1} cells (support a up to {float(g.length(M + 1) / 2):.3f}).  [{time.time()-t0:.0f}s]")
    print(f"  all reflection coefficients in (-1, 1): {all(abs(k) < 1 for k in ks)} ({len(ks)} computed);"
          f" max |k| = {mp.nstr(max(abs(k) for k in ks), 6)}")
    if show_table:
        print("  Lags m where a prime power n is in t_m. a = support of the section that first contains lag m;")
        print("  E/t0 = margin before the step (prediction error E_{m-1}); new = the prime power's part of t_m;")
        print("  new/E = that part in disk units (its shift of k_m on its own); k_m = actual coefficient.")
        print("     n     m      a      E_{m-1}/t_0     new/t_0        new/E_{m-1}        k_m          1-|k_m|")
        for n, lam in vm:
            L = mp.log(n)
            for m in range(1, len(ks) + 1):
                if abs(L - m * g.eps) < r * g.eps:
                    new = -lam / mp.sqrt(n) * (g.e(m, L) + g.e(m, -L))
                    k = ks[m - 1]
                    print(f"  {n:4d}  {m:4d}  {float(g.length(m + 1) / 2):6.3f}   {mp.nstr(E[m - 1] / t[0], 5):>12}"
                          f"   {mp.nstr(new / t[0], 5):>11}   {mp.nstr(new / E[m - 1], 5):>14}   {mp.nstr(k, 6):>12}"
                          f"   {mp.nstr(1 - abs(k), 4):>10}")
    print("  Margin along the support: a, E_N/t_0 (prediction error of the newest cell), lambda_min(T_N)/t_0:")
    step = max(1, int(round(0.2 / float(g.eps))))
    rows = []
    for N in range(1, len(E) + 1, step):
        rows.append(f"    a = {float(g.length(N) / 2):5.2f}   E = {mp.nstr(E[N - 1] / t[0], 4):>10}"
                    f"   lambda_min = {mp.nstr(min_eig(t, N), 4) if N <= 160 else '-':>10}")
    print("\n".join(rows))
    print(f"  [{time.time()-t0:.0f}s]", flush=True)
    return g, M, vm, sm, t, ks, E


# ------------------------------------------------------------------------- part 2: semilocal (one prime missing)
def semilocal(g, M, vm, sm):
    print(f"\nPart 2. Semilocal sections (r = {g.r}, eps = {mp.nstr(g.eps, 3)}): keep the real place and the primes"
          "\n  below p*, drop p* and all larger primes. First section that is not positive definite, against the first"
          "\n  section in which log p* appears.")
    for pstar in (2, 3, 5, 7, 11, 13):
        keep = lambda n, ps=pstar: next(d for d in range(2, n + 1) if n % d == 0) < ps
        pr = g.prime(M, vm, keep)
        t = [sm[m] + pr[m] for m in range(M + 1)]
        ks, E = levinson(t)
        first = next((m for m in range(1, M + 1) if abs(mp.log(pstar) - m * g.eps) < g.r * g.eps), None)
        bad = next((m + 1 for m, k in enumerate(ks) if abs(k) >= 1), None)
        if first is None:
            continue
        fa = float(g.length(first + 1) / 2)
        if bad is None:
            print(f"  p* = {pstar:2d}: enters at lag {first} (a = {fa:.3f}); still positive at the end (lag {len(ks)})")
        else:
            print(f"  p* = {pstar:2d}: enters at lag {first} (a = {fa:.3f}; (1/2) log p* = {float(mp.log(pstar)/2):.3f});"
                  f" first |k| >= 1 at lag {bad} (a = {float(g.length(bad + 1) / 2):.3f}), k = {mp.nstr(ks[-1], 5)}")
    print(f"  [{time.time()-t0:.0f}s]", flush=True)


# ------------------------------------------------------------------- part 3: how exact must the prime weights be?
def sensitivity(g, M, vm, sm, primes=(2, 3, 5, 7)):
    print(f"\nPart 3. Exactness of the weights (r = {g.r}, eps = {mp.nstr(g.eps, 3)}, support up to "
          f"{float(g.length(M + 1) / 2):.3f}): multiply Lambda(p^j) for one prime p (all powers) by (1 + eta);"
          "\n  smallest |eta| found (halving from 0.5) at which some section stops being positive definite.")
    for p in primes:
        res = []
        for sign in (1, -1):
            eta, last_bad = mp.mpf("0.5"), None
            for _it in range(80):
                vmx = [(n, l * (1 + sign * eta)) if is_pow(n, p) else (n, l) for n, l in vm]
                pr = g.prime(M, vmx)
                ks, _ = levinson([sm[m] + pr[m] for m in range(M + 1)])
                if any(abs(k) >= 1 for k in ks):
                    last_bad, eta = eta, eta / 2
                else:
                    break
            sgn = "+" if sign > 0 else "-"
            res.append(f"{sgn}{mp.nstr(last_bad, 3)} breaks, {sgn}{mp.nstr(eta, 3)} does not" if last_bad
                       else f"{sgn}0.5 does not break")
        print(f"  p = {p}: " + ";   ".join(res), flush=True)
    print(f"  [{time.time()-t0:.0f}s]", flush=True)


# ------------------------------------------------------------- part 4: the margin just before and after each entry
def before_after(g, M, vm, sm, t, ks):
    print(f"\nPart 4. Margin before and after each prime power enters (r = {g.r}, eps = {mp.nstr(g.eps, 3)}).")
    print("  N_b = last section without log n, N_a = N_b + 2r (first section holding all lags where n appears);")
    print("  lambda_min relative to t_0; 'without p' drops the prime p of n (all its powers) from N_a on.")
    print("     n    a(N_b)   lambda_min(N_b)   a(N_a)   lambda_min(N_a)   ratio a/b    without p at N_a")
    for n, lam in vm:
        L = mp.log(n)
        m1 = next((m for m in range(0, M + 1) if abs(L - m * g.eps) < g.r * g.eps), None)
        if m1 is None or m1 + 2 * g.r > M + 1 or n > 13:
            continue
        Nb, Na = m1, m1 + 2 * g.r
        p = next(d for d in range(2, n + 1) if n % d == 0)
        lb, la = min_eig(t, Nb), min_eig(t, Na)
        pr = g.prime(M, vm, lambda q, p=p: not is_pow(q, p))
        tw = [sm[m] + pr[m] for m in range(M + 1)]
        lw = min_eig(tw, Na)
        print(f"  {n:4d}   {float(g.length(Nb) / 2):6.3f}   {mp.nstr(lb, 4):>12}     {float(g.length(Na) / 2):6.3f}"
              f"   {mp.nstr(la, 4):>12}     {mp.nstr(la / lb, 3):>8}     {mp.nstr(lw, 4):>12}", flush=True)
    print("  Reflection coefficients k_m by lag (* = a prime power sits at this lag):")
    row = []
    for m, k in enumerate(ks, start=1):
        star = "*" if any(abs(mp.log(n) - m * g.eps) < g.r * g.eps for n, _ in vm) else " "
        row.append(f"{m:3d}{star}{mp.nstr(k, 3):>9}")
    for i in range(0, len(row), 8):
        print("   " + " ".join(row[i:i + 8]))
    sel = lambda flag: [abs(k) for m, k in enumerate(ks, start=1)
                        if any(abs(mp.log(n) - m * g.eps) < g.r * g.eps for n, _ in vm) == flag]
    for flag, name in ((True, "lags with a prime power"), (False, "lags without")):
        v = sel(flag)
        if v:
            print(f"  {name}: {len(v)} lags, mean |k| = {mp.nstr(sum(v) / len(v), 3)}, max |k| = {mp.nstr(max(v), 3)}")
    print(f"  [{time.time()-t0:.0f}s]", flush=True)


if __name__ == "__main__":
    check_against_zeros()
    for (eps, r, amax) in ((0.05, 1, 1.25), (0.05, 3, 1.25)):
        g, M, vm, sm, t, ks, E = run(eps, r, amax)
        semilocal(g, M, vm, sm)
        sensitivity(g, M, vm, sm)
    g, M, vm, sm, t, ks, E = run(0.025, 3, 1.25, show_table=False)
    semilocal(g, M, vm, sm)
    before_after(g, M, vm, sm, t, ks)
    print(f"\n[done] {time.time()-t0:.0f}s")
