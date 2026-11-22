"""c8a-saturation N1 (PREREG.md): 2D Z2 lattice gauge theory on the N x N torus, exact by brute force.

Checks 1 - 2P = tanh(beta)^(N^2) and the Lean bound B >= |1 - 2P| (where q < 1).
The configurations are counted exactly by (sum of plaquettes, sheet plaquette) and the sums are evaluated in 60-digit
decimal arithmetic: the first run in double precision (z2_exact_2d_float.log) failed the 1e-10 criterion only through
cancellation at N = 3, where |1 - 2P| is about 1e-12.
Run: py z2_exact_2d.py > z2_exact_2d.log
"""
import itertools
import math
from collections import Counter
from decimal import Decimal, getcontext

getcontext().prec = 60


def counts(N):
    """Exact integer counts of configurations by (sum_p sigma_p, sigma_sheet)."""
    c = Counter()
    nl = 2 * N * N
    for bits in itertools.product((1, -1), repeat=nl):
        U0 = [bits[i * N:(i + 1) * N] for i in range(N)]
        U1 = [bits[N * N + i * N:N * N + (i + 1) * N] for i in range(N)]
        s = 0
        sheet = 0
        for x in range(N):
            for y in range(N):
                pl = U0[x][y] * U1[(x + 1) % N][y] * U0[x][(y + 1) % N] * U1[x][y]
                s += pl
                if x == 0 and y == 0:
                    sheet = pl
        c[(s, sheet)] += 1
    return c


def flip(c, beta):
    b = Decimal(repr(beta))
    Z = sum(Decimal(n) * (b * s).exp() for (s, sh), n in c.items())
    Ztw = sum(Decimal(n) * (b * (s - 2 * sh)).exp() for (s, sh), n in c.items())
    return Ztw / (Z + Ztw), (Z - Ztw) / (Z + Ztw)


def tanh_dec(beta):
    b = Decimal(repr(beta))
    e = (2 * b).exp()
    return (e - 1) / (e + 1)


def lean_bound(d, N, beta):
    p = 1 - math.exp(-2 * abs(beta))
    q = 2 * (d - 1) * p
    if q >= 1:
        return None
    return (N ** d * p * q ** (N - 1) / (1 - q)) ** N


def main():
    ok = True
    print("N  beta   P                      1-2P            tanh(beta)^(N^2)  relerr     LeanB(d=2)")
    for N in (2, 3):
        c = counts(N)
        assert sum(c.values()) == 2 ** (2 * N * N)
        for beta in (-0.3, 0.05, 0.2, 0.5, 1.0):
            P, lhs = flip(c, beta)
            rhs = tanh_dec(beta) ** (N * N)
            rel = abs(lhs - rhs) / abs(rhs)
            B = lean_bound(2, N, beta)
            ok &= rel < Decimal("1e-10")
            if B is not None:
                ok &= B >= abs(float(lhs))
            Bs = "None (q >= 1)" if B is None else f"{B:.3e}"
            print(f"{N}  {beta:+.2f}  {float(P):.18f}  {float(lhs):+.6e}  {float(rhs):+.6e}   {float(rel):.1e}  {Bs}")
    print("PASS" if ok else "FAIL")


if __name__ == "__main__":
    main()
