#!/usr/bin/env python3
"""GRH attempt, variational form: the ground state of a finite section of Weil's form.

Reuses the grid of induction.py (cells = centred B-splines of order 2r, step eps; Toeplitz sections of Weil's form).
For a section of support a (N cells) it computes:
  - lambda_min (relative to t_0) and the gap to the next eigenvalue (is the ground state simple?), and whether the
    ground state vector is symmetric or antisymmetric;
  - the zeros of the ground-state polynomial sum_j v_j z^j: their distance from the unit circle (Pisarenko /
    Caratheodory-Fejer: on the circle whenever lambda_min is simple, positive or not), and the angles arg(z)/eps
    against the ordinates of the zeta zeros;
  - the first variation of the margin under Lambda(p^j) -> (1+s) Lambda(p^j) (Hellmann-Feynman: v^T P_p v / t_0),
    i.e. whether the arithmetic configuration is a stationary point (an optimum) of the margin at this scale;
  - the same ground-state zeros for the archimedean place alone (no primes), as the control.
Run from anywhere: python3 docs/rh-guide/grh/variational.py > docs/rh-guide/grh/variational.log
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp  # noqa: E402
from induction import Grid, vm_list, is_pow  # noqa: E402

mp.mp.dps = 60
t0 = time.time()
GAMMA = [mp.zetazero(k).imag for k in range(1, 41)]


def section(t, N):
    T = mp.matrix(N, N)
    for i in range(N):
        for j in range(N):
            T[i, j] = t[abs(i - j)]
    return T


def ground(t, N):
    ev, V = mp.eigsy(section(t, N))
    order = sorted(range(N), key=lambda i: ev[i])
    i0, i1 = order[0], order[1]
    v = [V[j, i0] for j in range(N)]
    return ev[i0], ev[i1], v


def nearest(g):
    return min(GAMMA, key=lambda x: abs(x - g))


def analyse(g, t, N, label, parts=None):
    lam, lam1, v = ground(t, N)
    sym = max(abs(v[j] - v[N - 1 - j]) for j in range(N)) < mp.mpf(10) ** -30
    anti = max(abs(v[j] + v[N - 1 - j]) for j in range(N)) < mp.mpf(10) ** -30
    roots = mp.polyroots(list(reversed(v)), maxsteps=400, extraprec=400)
    dev = max(abs(abs(z) - 1) for z in roots)
    ang = sorted(float(mp.arg(z) / g.eps) for z in roots if mp.im(z) > 0)
    print(f"  {label}: a = {float(g.length(N) / 2):.3f}, N = {N}: lambda_min/t0 = {mp.nstr(lam / t[0], 4)}, "
          f"next/t0 = {mp.nstr(lam1 / t[0], 4)}, ground state {'even' if sym else 'odd' if anti else 'neither'}; "
          f"max ||z|-1| = {mp.nstr(dev, 3)}")
    low = [x for x in ang if x < 52]
    print("    angles/eps below 52: " + ", ".join(f"{x:.3f}" for x in low))
    print("    nearest zeta ordinate, difference: "
          + ", ".join(f"{float(nearest(x)):.3f} ({x - float(nearest(x)):+.1e})" for x in low))
    if parts:
        out = []
        for p, P in parts:
            d = sum(v[i] * v[j] * P[abs(i - j)] for i in range(N) for j in range(N)) / t[0]
            out.append(f"p={p}: {mp.nstr(d, 3)}")
        print("    d(lambda_min/t0)/ds at s=0 for Lambda(p^j) -> (1+s)Lambda(p^j): " + "; ".join(out)
              + f"   (lambda_min/t0 itself {mp.nstr(lam / t[0], 3)})")


def run(eps, r, supports):
    g = Grid(eps, r)
    Nmax = max(int(mp.floor(2 * a / g.eps)) - r + 1 for a in supports)
    M = Nmax
    vm = vm_list(int(mp.exp(g.length(M + 1))) + 2)
    sm = g.smooth(M)
    pr = g.prime(M, vm)
    t = [sm[m] + pr[m] for m in range(M + 1)]
    parts = [(p, g.prime(M, vm, lambda n, p=p: is_pow(n, p))) for p in (2, 3, 5, 7)]
    print(f"\nGrid r = {r}, eps = {eps}  (first zeta ordinates: "
          + ", ".join(f"{float(x):.3f}" for x in GAMMA[:10]) + ")")
    for a in supports:
        N = int(mp.floor(2 * a / g.eps)) - r + 1
        analyse(g, t, N, "full", parts)
    N = int(mp.floor(2 * supports[-1] / g.eps)) - r + 1
    analyse(g, sm, N, "archimedean place only (control)")
    print(f"  [{time.time() - t0:.0f}s]", flush=True)


if __name__ == "__main__":
    run(0.05, 1, (0.6, 0.9, 1.25))
    run(0.05, 3, (0.6, 0.9, 1.25))
    print(f"\n[done] {time.time() - t0:.0f}s")
