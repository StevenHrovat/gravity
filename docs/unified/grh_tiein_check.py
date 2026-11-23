"""Third-layer check for GRH-TIE-IN.md (CPU, minutes at most, no saved data needed).

Function-field instance of the GRH ledger column. A genus-2 curve y^2 = f(x), deg f = 5 (one point at infinity), over F_p.
Rationality (classical) says N_m = #C(F_{p^m}) = p^m + 1 - sum alpha_i^m with four Frobenius eigenvalues alpha_i.

This script counts N_1, N_2, N_3, N_4 DIRECTLY, by listing the elements of F_{p^m} (no use of rationality, no use of
Weil's bound), and then checks three things that the Lean file ProofPhase/GRH/TieInFF.lean states:

  1. Rationality: N_3 and N_4 agree with the values predicted from N_1, N_2 alone (Newton sums of the quartic
     L-polynomial with a_3 = p a_1 and a_4 = p^2). The moments beyond g are spanned by the prime side.
  2. The moments of the grid form come from the counts alone: t(m) = (p^m + 1 - N_m) / p^(m/2), t(0) = 2g = 4.
  3. The closure (Lean: curve_sections). The Toeplitz sections of t of size 1..4 are positive definite (|k| < 1 at every
     step before the closure) and the section of size 5 = 2g + 1 is singular (|k_4| = 1).
Control: one count N_4 changed by +1 (a miscount): the sections no longer pass.

Run: python docs/unified/grh_tiein_check.py > docs/unified/grh_tiein_check.log
"""
import numpy as np
from collections import Counter
from sympy import Poly, symbols, ZZ
from sympy.polys.galoistools import gf_irreducible

np.set_printoptions(precision=6, suppress=True)


class Field:
    """F_{p^k} = F_p[w]/(m(w)), m monic irreducible of degree k. Elements are tuples of k ints, low degree first."""

    def __init__(self, p, k):
        self.p, self.k = p, k
        m = gf_irreducible(k, p, ZZ)  # high degree first, monic
        self.red = [(-int(c)) % p for c in m[:0:-1]]  # w^k = sum red[i] w^i, i = 0..k-1
        self.elements = [tuple(v) for v in np.ndindex(*([p] * k))]

    def mul(self, x, y):
        p, k = self.p, self.k
        prod = [0] * (2 * k - 1)
        for i, a in enumerate(x):
            if a:
                for j, b in enumerate(y):
                    prod[i + j] += a * b
        for d in range(2 * k - 2, k - 1, -1):
            c = prod[d] % p
            if c:
                for i, r in enumerate(self.red):
                    prod[d - k + i] += c * r
            prod[d] = 0
        return tuple(v % p for v in prod[:k])

    def add(self, x, y):
        return tuple((a + b) % self.p for a, b in zip(x, y))

    def const(self, c):
        return (c % self.p,) + (0,) * (self.k - 1)


def count_points(coeffs, p, k):
    """N_k = #C(F_{p^k}) for y^2 = f(x), deg f = 5, one point at infinity, by listing every x and every y."""
    F = Field(p, k)
    sq = Counter(F.mul(y, y) for y in F.elements)  # number of y with y^2 = v
    n = 1
    for x in F.elements:
        v = F.const(0)
        for c in reversed(coeffs):  # Horner
            v = F.add(F.mul(v, x), F.const(c))
        n += sq.get(v, 0)
    return n


def power_sums(n1, n2, p):
    """s_1..s_4 of the four Frobenius eigenvalues from N_1, N_2 (rationality with deg 4 and the functional equation)."""
    s1 = p + 1 - n1
    s2 = p * p + 1 - n2
    e1 = s1
    e2 = (s1 * s1 - s2) // 2
    e3, e4 = p * e1, p * p
    s3 = e1 * s2 - e2 * s1 + 3 * e3
    s4 = e1 * s3 - e2 * s2 + e3 * s1 - 4 * e4
    return (s1, s2, s3, s4), (e1, e2)


def szego_k(t):
    a = np.array([1.0])
    E = t[0]
    ks = []
    for m in range(1, len(t)):
        acc = sum(a[j] * t[m - j] for j in range(m))
        k = -acc / E
        ks.append(k)
        a = np.concatenate([a, [0]]) + k * np.concatenate([[0], a[::-1]])
        E = E * (1 - k * k)
    return ks


def sections(t):
    """Least eigenvalue of the Toeplitz section of size s = 1..len(t) (t(0..len-1), real symmetric)."""
    out = []
    for s in range(1, len(t) + 1):
        T = np.array([[t[abs(i - j)] for j in range(s)] for i in range(s)])
        out.append(float(np.linalg.eigvalsh(T)[0]))
    return out


x = symbols("x")
curves = [(7, [1, 2, 0, 3, 0, 1]), (11, [3, 1, 4, 1, 5, 1]), (13, [2, 7, 1, 8, 2, 1])]

print("== grh_tiein_check: genus-2 curves over F_p, N_1..N_4 counted directly over F_p, F_p^2, F_p^3, F_p^4")
allok = True
for p, coeffs in curves:
    f = Poly(sum(c * x**i for i, c in enumerate(coeffs)), x, modulus=p)
    sqfree = f.discriminant() % p != 0
    N = [count_points(coeffs, p, k) for k in (1, 2, 3, 4)]
    (s1, s2, s3, s4), (e1, e2) = power_sums(N[0], N[1], p)
    pred3, pred4 = p**3 + 1 - s3, p**4 + 1 - s4
    ok_rat = (N[2] == pred3) and (N[3] == pred4)
    alphas = np.roots([1, -e1, e2, -p * e1, p * p])
    dist = min(abs(a - b) for i, a in enumerate(alphas) for b in alphas[i + 1:])
    t = [4.0] + [(p**m + 1 - N[m - 1]) / p ** (m / 2) for m in range(1, 5)]
    lam = sections(t)
    ks = szego_k(t)
    defin = all(l > 1e-9 for l in lam[:4])
    sing = abs(lam[4]) < 1e-9
    allok &= ok_rat and defin and sing and sqfree
    print(f"p={p:3d} f={coeffs} squarefree={sqfree}")
    print(f"    counted   N_1..N_4 = {N}")
    print(f"    predicted N_3, N_4 from N_1, N_2 = {pred3}, {pred4}   agree: {ok_rat}")
    print(f"    |alpha_i|/sqrt(p) = {np.abs(alphas) / np.sqrt(p)}  (min distance between atoms {dist:.3f})")
    print(f"    t(0..4) from counts alone = {np.array(t)}")
    print(f"    least eigenvalue of the section of size 1..5 = {[f'{l:.3e}' for l in lam]}")
    print(f"    sizes 1..4 definite: {defin}   size 5 (= 2g + 1) singular: {sing}")
    print(f"    |k_1..k_4| = {[round(float(abs(k)), 9) for k in ks]}")
    # control: one wrong count
    tc = list(t)
    tc[4] = (p**4 + 1 - (N[3] + 1)) / p**2
    lamc = sections(tc)
    print(f"    control (N_4 + 1): least eigenvalues of sizes 1..5 = {[f'{l:.3e}' for l in lamc]}  "
          f"-> the sections no longer pass: {not (all(l > 1e-9 for l in lamc[:4]) and abs(lamc[4]) < 1e-9)}")
print()
print(f"== all curves pass: {allok}")
