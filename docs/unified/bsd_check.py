"""Birch and Swinnerton-Dyer: CPU checks for the two example curves of BSD.md (Lean: ProofPhase/Unified/BSDCore.lean,
BSDAPI.lean). Numerical, a third layer that can refute or guide, never establish.
  (1) Point counts mod p and Hasse's bound |a_p| <= 2 sqrt p for every prime p < 20000 (exact integer arithmetic), for
      32a2: y^2 = x^3 - x (rank 0) and 37a1: y^2 + y = x^3 - x (rank 1). The Lean #eval values of a_p for 32a2 are
      re-derived here.
  (2) The Frobenius encoder: cos(theta_p) = a_p / (2 sqrt p) lies in [-1, 1] and N_p = |1 - alpha_p|^2.
  (3) L(E, 1) for 32a2 (root number +1) and L'(E, 1) for 37a1 (root number -1) from the rapidly converging series
      L^{(r)}(E, 1) = 2 sum a_n / n * G_r(2 pi n / sqrt N), G_0(x) = exp(-x), G_1(x) = E_1(x).
  (4) The rational point (0, 0) on 37a1 and its first multiples: the denominators grow, so the point has infinite order
      (Nagell-Lutz: torsion points of an integral model have integral coordinates).
  (5) The Euler ledger: partial products prod_{p <= x} N_p / p, normalised by (log x)^r, at several x, next to the
      constant sqrt(2) e^{r gamma} r! / L^{(r)}(E, 1) of Goldfeld's theorem (recalled, see BSD.md section 4).
  (6) The refined formula, numerically: the real period Omega = integral of |dx/(2y + a1 x + a3)| over E(R) (both
      components when the discriminant is positive), and L^{(r)}(E, 1)/(r! Omega) next to the recalled right-hand side
      (32a2: c_2 Sha / T^2 = 2 * 1 / 16; 37a1: the regulator 0.0511114082 with c_37 = Sha = T = 1)."""
from fractions import Fraction
from math import exp, log, pi, sqrt, isqrt

import mpmath

PMAX = 20000
NTERMS = 3000


def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, isqrt(n) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i in range(n + 1) if sieve[i]]


def affine_count(a, p):
    """Number of affine solutions mod p of y^2 + a1 x y + a3 y = x^3 + a2 x^2 + a4 x + a6 (singular point included)."""
    a1, a2, a3, a4, a6 = (c % p for c in a)
    # count, for every x, the y with y^2 + (a1 x + a3) y - f(x) = 0
    sq = [0] * p
    for y in range(p):
        sq[y * y % p] += 1
    n = 0
    for x in range(p):
        b = (a1 * x + a3) % p
        c = (x * x * x + a2 * x * x + a4 * x + a6) % p
        if p == 2:
            n += sum(1 for y in range(2) if (y * y + b * y - c) % 2 == 0)
        else:
            # (2y + b)^2 = b^2 + 4c
            n += sq[(b * b + 4 * c) % p]
    return n


CURVES = {
    "32a2": dict(a=(0, 0, 0, -1, 0), N=32, w=+1, r=0, bad=[2]),
    "37a1": dict(a=(0, 0, 1, -1, 0), N=37, w=-1, r=1, bad=[37]),
}

PR = primes_upto(PMAX)


def ap_table(a):
    """a_p = p - #affine (good p: p + 1 - #E(F_p); bad p: 1 split, -1 nonsplit, 0 additive)."""
    return {p: p - affine_count(a, p) for p in PR}


def an_series(ap, bad, n_max):
    an = [0] * (n_max + 1)
    an[1] = 1
    # a_{p^k} by the Hecke recursion, then multiplicativity
    pk = {}
    for p in PR:
        if p > n_max:
            break
        vals = [1, ap[p]]
        q = p
        while q * p <= n_max:
            q *= p
            if p in bad:
                vals.append(vals[-1] * ap[p])
            else:
                vals.append(ap[p] * vals[-1] - p * vals[-2])
        pk[p] = vals
    for n in range(2, n_max + 1):
        m, val = n, 1
        for p in PR:
            if p * p > m:
                break
            if m % p == 0:
                k = 0
                while m % p == 0:
                    m //= p
                    k += 1
                val *= pk[p][k]
        if m > 1:
            val *= pk[m][1]
        an[n] = val
    return an


def main():
    gamma = float(mpmath.euler)
    for name, c in CURVES.items():
        print(f"== {name}: a = {c['a']}, conductor {c['N']}, root number {c['w']:+d}, rank {c['r']}")
        ap = ap_table(c["a"])
        worst = max(abs(ap[p]) / (2 * sqrt(p)) for p in PR)
        hasse_ok = all(ap[p] * ap[p] <= 4 * p for p in PR)
        print(f"(1) Hasse a_p^2 <= 4p for all {len(PR)} primes below {PMAX}: {hasse_ok}; max |a_p|/(2 sqrt p) = {worst:.6f}")
        print("    a_p, p = 2..37:", [ap[p] for p in PR if p <= 37])
        # (2) encoder
        enc_ok = True
        for p in PR[:200]:
            if p in c["bad"]:
                continue
            cth = ap[p] / (2 * sqrt(p))
            alpha = complex(ap[p] / 2, sqrt(max(p - ap[p] ** 2 / 4, 0.0)))
            Np = p + 1 - ap[p]
            enc_ok &= (-1 <= cth <= 1) and abs(abs(1 - alpha) ** 2 - Np) < 1e-8 and abs(abs(alpha) ** 2 - p) < 1e-8
        print(f"(2) encoder: cos(theta_p) in [-1, 1], N_p = |1 - alpha_p|^2, |alpha_p|^2 = p for the first 200 primes: {enc_ok}")
        # (3) L-value
        an = an_series(ap, c["bad"], NTERMS)
        x0 = 2 * pi / sqrt(c["N"])
        if c["r"] == 0:
            L = 2 * sum(an[n] / n * exp(-x0 * n) for n in range(1, NTERMS + 1))
            print(f"(3) L(E, 1) = {L:.12f}  (series, {NTERMS} terms)")
        else:
            L = 2 * sum(an[n] / n * float(mpmath.e1(x0 * n)) for n in range(1, NTERMS + 1))
            L0 = 2 * sum(an[n] / n * exp(-x0 * n) for n in range(1, NTERMS + 1)) * (1 + c["w"]) / 2
            print(f"(3) L(E, 1) = {L0:.3e} (forced 0 by w = -1); L'(E, 1) = {L:.12f}  (series, {NTERMS} terms)")
        # (4) the point (0, 0) on 37a1
        if name == "37a1":
            a1, a2, a3, a4, a6 = c["a"]

            def on(P):
                x, y = P
                return y * y + a1 * x * y + a3 * y == x ** 3 + a2 * x * x + a4 * x + a6

            def add(P, Q):
                if P is None:
                    return Q
                if Q is None:
                    return P
                (x1, y1), (x2, y2) = P, Q
                if x1 == x2 and y1 + y2 + a1 * x2 + a3 == 0:
                    return None
                if x1 == x2:
                    lam = (3 * x1 * x1 + 2 * a2 * x1 + a4 - a1 * y1) / (2 * y1 + a1 * x1 + a3)
                else:
                    lam = (y2 - y1) / (x2 - x1)
                nu = y1 - lam * x1
                x3 = lam * lam + a1 * lam - a2 - x1 - x2
                y3 = -(lam + a1) * x3 - nu - a3
                return (x3, y3)

            P = (Fraction(0), Fraction(0))
            Q, mults = None, []
            for k in range(1, 9):
                Q = add(Q, P)
                assert Q is not None and on(Q)
                mults.append(Q)
            dens = [max(q[0].denominator, q[1].denominator) for q in mults]
            print(f"(4) (0, 0) on 37a1: {on(P)}; denominators of kP, k = 1..8: {dens}")
            print(f"    5P = ({mults[4][0]}, {mults[4][1]}): not integral, so P is not torsion (Nagell-Lutz)")
        # (5) Euler ledger
        r = c["r"]
        target = sqrt(2) * exp(r * gamma) * (1 if r == 0 else 1) / L
        out = []
        prod = 1.0
        marks = [100, 1000, 5000, 20000]
        mi = 0
        for p in PR:
            prod *= (p + 1 - ap[p]) / p if p not in c["bad"] else (p - ap[p]) / p
            while mi < len(marks) and (PR.index(p) + 1 == len(PR) or PR[PR.index(p) + 1] > marks[mi]):
                out.append((marks[mi], prod / log(marks[mi]) ** r))
                mi += 1
            if mi >= len(marks):
                break
        # (6) the real period
        a1, a2, a3, a4, a6 = c["a"]
        # (2y + a1 x + a3)^2 = 4 x^3 + b2 x^2 + 2 b4 x + b6 =: g(x); |omega| = dx / sqrt(g) on each half, two halves per oval
        b2, b4, b6 = a1 * a1 + 4 * a2, 2 * a4 + a1 * a3, a3 * a3 + 4 * a6
        roots = sorted(float(z.real) for z in mpmath.polyroots([4, b2, 2 * b4, b6]) if abs(z.imag) < 1e-12)
        g = lambda x: 4 * x ** 3 + b2 * x ** 2 + 2 * b4 * x + b6
        Om = 2 * mpmath.quad(lambda x: 1 / mpmath.sqrt(abs(g(x))), [roots[-1], roots[-1] + 1, mpmath.inf])
        if len(roots) == 3:
            Om += 2 * mpmath.quad(lambda x: 1 / mpmath.sqrt(abs(g(x))), [roots[0], roots[1]])
        rhs = 2 / 16 if name == "32a2" else 0.0511114082
        print(f"(6) Omega = {float(Om):.10f} ({len(roots)} real roots); L^(r)(1)/(r! Omega) = {L / float(Om):.10f};"
              f" recalled right-hand side {rhs:.10f}")
        print("(5) prod_{p <= x} N_p/p / (log x)^r:", ", ".join(f"x={x}: {v:.4f}" for x, v in out),
              f"| sqrt2 e^(r gamma) r!/L^(r)(1) = {target:.4f}")


if __name__ == "__main__":
    main()
