#!/usr/bin/env python3
"""GRH attempt, transfer round: pairs of primes, per-prime contraction coefficients, two-term bounds.

On the grid of induction.py (cells = centred B-splines of order 2r, step eps), Weil's form on a section splits as
A (pole + real place) + sum_p P_p (the block of the prime p, all its powers).
  Part 1 (pairs): lambda_min of A + sum_{p in S} P_p for every subset S of the primes present at a support:
          which sets of primes certify positivity, and whether a pair certifies what neither prime alone does.
  Part 2 (per-prime coefficients): Levinson factors (1 - k_m^2) of the whole form, grouped by the prime whose power sits
          at lag m; eta_p = product over those lags; the rest (lags with no prime power) separately.
  Part 3 (two-term bound): Weyl's bound lambda_min(A) + lambda_min(sum P) (confinement term + worst resolvable
          prime alignment) against the true lambda_min(A + sum P).
Run from anywhere: python3 docs/rh-guide/grh/transfer.py > docs/rh-guide/grh/transfer.log
"""
import os
import sys
import time
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp  # noqa: E402
from induction import Grid, vm_list, is_pow, levinson  # noqa: E402

mp.mp.dps = 60
t0 = time.time()


def lam_min(t, N):
    T = mp.matrix(N, N)
    for i in range(N):
        for j in range(N):
            T[i, j] = t[abs(i - j)]
    return min(mp.eigsy(T, eigvals_only=True))


def setup(eps, r, amax):
    g = Grid(eps, r)
    M = int(mp.floor(2 * amax / g.eps)) - r + 1
    vm = vm_list(int(mp.exp(g.length(M + 1))) + 2)
    sm = g.smooth(M)
    primes = sorted({n for n, _ in vm if all(n % q for q in range(2, n))})
    blocks = {p: g.prime(M, vm, lambda n, p=p: is_pow(n, p)) for p in primes}
    tot = [sm[m] + sum(blocks[p][m] for p in primes) for m in range(M + 1)]
    return g, M, vm, sm, primes, blocks, tot


def part1(g, sm, primes, blocks, tot, supports):
    T0 = tot[0]
    print(f"\nPart 1. Which sets of primes certify positivity (r = {g.r}, eps = {float(g.eps)}); lambda_min / t_0 of "
          "A + sum_{p in S} P_p.")
    for a in supports:
        N = int(mp.floor(2 * a / g.eps)) - g.r + 1
        present = [p for p in primes if any(blocks[p][m] != 0 for m in range(N))]
        rows = []
        for k in range(len(present) + 1):
            for S in combinations(present, k):
                t = [sm[m] + sum(blocks[p][m] for p in S) for m in range(N)]
                rows.append((S, lam_min(t, N) / T0))
        pos = [S for S, v in rows if v > 0]
        print(f"  a = {float(g.length(N) / 2):.3f} (N = {N}), primes present {present}:")
        print("    " + "; ".join(f"{{{','.join(map(str, S))}}}: {mp.nstr(v, 3)}" for S, v in rows))
        print(f"    positive sets: {['{' + ','.join(map(str, S)) + '}' for S in pos]}")
        if len(present) >= 2:
            d = dict(rows)
            p, q = present[0], present[1]
            syn = d[(p, q)] - d[(p,)] - d[(q,)] + d[()]
            print(f"    pair synergy for {{{p},{q}}}: lambda(A+P{p}+P{q}) - lambda(A+P{p}) - lambda(A+P{q}) + "
                  f"lambda(A) = {mp.nstr(syn, 3)}")
    print(f"  [{time.time() - t0:.0f}s]", flush=True)


def part2(g, M, vm, tot):
    ks, E = levinson(tot)
    print(f"\nPart 2. Per-prime factors of the margin (r = {g.r}, eps = {float(g.eps)}, lags 1..{len(ks)}): "
          "E_N / t_0 = product of (1 - k_m^2).")
    groups = {}
    for m in range(1, len(ks) + 1):
        owners = sorted({p for n, _ in vm for p in [min(q for q in range(2, n + 1) if n % q == 0)]
                         if is_pow(n, p) and abs(mp.log(n) - m * g.eps) < g.r * g.eps})
        key = owners[0] if len(owners) == 1 else (tuple(owners) if owners else "none")
        groups.setdefault(key, []).append(1 - ks[m - 1] ** 2)
    total = mp.mpf(1)
    for key, fac in groups.items():
        pr = mp.fprod(fac)
        total *= pr
        print(f"  {str(key):>8}: {len(fac):3d} lags, product {mp.nstr(pr, 4)}, smallest factor {mp.nstr(min(fac), 3)}")
    print(f"  all lags: product {mp.nstr(total, 4)} = E_N / t_0 = {mp.nstr(E[-1] / E[0], 4)}")
    print(f"  [{time.time() - t0:.0f}s]", flush=True)


def part3(g, sm, primes, blocks, tot, supports):
    T0 = tot[0]
    print(f"\nPart 3. Two-term (Weyl) bound (r = {g.r}, eps = {float(g.eps)}): lambda_min(A) + lambda_min(sum P) "
          "against lambda_min(A + sum P), relative to t_0.")
    print("    a     lambda_min(A)   lambda_min(sum P)   Weyl bound    true lambda_min")
    for a in supports:
        N = int(mp.floor(2 * a / g.eps)) - g.r + 1
        P = [sum(blocks[p][m] for p in primes) for m in range(N)]
        lA, lP, lW = lam_min(sm, N) / T0, lam_min(P, N) / T0, lam_min(tot, N) / T0
        print(f"  {float(g.length(N) / 2):.3f}  {mp.nstr(lA, 4):>12}  {mp.nstr(lP, 4):>16}  {mp.nstr(lA + lP, 4):>12}"
              f"  {mp.nstr(lW, 4):>14}")
    print(f"  [{time.time() - t0:.0f}s]", flush=True)


if __name__ == "__main__":
    g, M, vm, sm, primes, blocks, tot = setup(0.05, 3, 1.25)
    part1(g, sm, primes, blocks, tot, (0.575, 0.65, 0.75, 0.875, 0.95, 1.05, 1.15, 1.225))
    part2(g, M, vm, tot)
    part3(g, sm, primes, blocks, tot, (0.35, 0.45, 0.575, 0.875, 1.225))
    g, M, vm, sm, primes, blocks, tot = setup(0.05, 1, 1.25)
    part2(g, M, vm, tot)
    part3(g, sm, primes, blocks, tot, (0.35, 0.45, 0.575, 0.875, 1.225))
    print(f"\n[done] {time.time() - t0:.0f}s")
