#!/usr/bin/env python3
"""GRH attempt, Tate round: can Weil positivity be assembled place by place?

Weil's form on a grid section (induction.py's grid: cells = centred B-splines of order 2r, step eps) splits by places:
  A   = pole + real place (the archimedean local term, with the pole),
  P_p = the local term of the prime p (all its powers), a Toeplitz block living only at lags near k log p, k >= 1.
Local terms at different primes live on disjoint lattices k log p (unique factorisation), so the only thing places can
exchange is a multiple of the identity (the lag-0 entry). Place-by-place positivity with such exchanges means:
  there are a_v with sum a_v = 0, A + a_inf I >= 0 and P_p + a_p I >= 0 for every p,
which holds exactly when  lambda_min(A) >= sum_p c_p,  c_p = -lambda_min(P_p) (>= 0, since P_p has zero diagonal).
The script prints both sides and the true lambda_min of the whole form, all relative to t_0.
Run from anywhere: python3 docs/rh-guide/grh/tate.py > docs/rh-guide/grh/tate.log
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp  # noqa: E402
from induction import Grid, vm_list, is_pow  # noqa: E402

mp.mp.dps = 60
t0 = time.time()


def lam_min(t, N):
    T = mp.matrix(N, N)
    for i in range(N):
        for j in range(N):
            T[i, j] = t[abs(i - j)]
    return min(mp.eigsy(T, eigvals_only=True))


def run(eps, r, supports):
    g = Grid(eps, r)
    M = max(int(mp.floor(2 * a / g.eps)) - r + 1 for a in supports)
    vm = vm_list(int(mp.exp(g.length(M + 1))) + 2)
    sm = g.smooth(M)
    primes = sorted({n for n, _ in vm if all(n % q for q in range(2, n))})
    blocks = {p: g.prime(M, vm, lambda n, p=p: is_pow(n, p)) for p in primes}
    tot = [sm[m] + sum(blocks[p][m] for p in primes) for m in range(M + 1)]
    T0 = tot[0]
    print(f"\nGrid r = {r}, eps = {eps}. All values relative to t_0. Zero diagonal of every P_p: "
          + ", ".join(f"p={p}: {mp.nstr(blocks[p][0], 2)}" for p in primes))
    print("   a     N  lambda_min(A)   c_p = -lambda_min(P_p) for the primes present            sum c_p    "
          "slack = lambda_min(A) - sum c_p   lambda_min(whole)")
    for a in supports:
        N = int(mp.floor(2 * a / g.eps)) - r + 1
        lA = lam_min(sm, N) / T0
        cs = []
        for p in primes:
            if any(blocks[p][m] != 0 for m in range(N)):
                cs.append((p, -lam_min(blocks[p], N) / T0))
        sc = sum(c for _, c in cs)
        lw = lam_min(tot, N) / T0
        print(f"  {float(g.length(N) / 2):.3f} {N:3d}  {mp.nstr(lA, 4):>11}   "
              + ", ".join(f"{p}: {mp.nstr(c, 3)}" for p, c in cs).ljust(58)
              + f" {mp.nstr(sc, 4):>9}    {mp.nstr(lA - sc, 4):>12}                  {mp.nstr(lw, 3)}", flush=True)
    print(f"  [{time.time() - t0:.0f}s]")


if __name__ == "__main__":
    run(0.05, 3, (0.3, 0.35, 0.375, 0.4, 0.425, 0.45, 0.5, 0.6, 0.9, 1.225))
    run(0.05, 1, (0.3, 0.35, 0.375, 0.4, 0.45, 0.6, 0.9, 1.225))
    print(f"\n[done] {time.time() - t0:.0f}s")
