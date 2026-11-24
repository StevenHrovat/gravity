"""Numerical check of the explicit formula in the exact normalisation of `ProofPhase/GRH/ExplicitFormula.lean`.

Checks `sum_rho H(rho) = efRHS c g`, where (see the Lean file)
  H(s)      = int g(x) e^{(s - 1/2) x} dx                    (`laplace`)
  efRHS c g = H(1) + H(0) - (P(g) + P(g~)) + (A(g) + A(g~)) / 2
  P(g)      = sum_n Lambda(n) n^{-1/2} g(log n)               (`primeSum`)
  A(g)      = (1/2 pi) int (psi(s/2) - log pi) H(s) dt, s = c + i t   (`archTerm`, line Re s = c)
  g~(x)     = g(-x)                                           (`refl`)
for shifted Gaussians g(x) = exp(-(x - a)^2 / (2 sigma^2)), H(s) = sigma sqrt(2 pi) exp(a w + sigma^2 w^2 / 2), w = s - 1/2.
The Gaussian is not compactly supported, but the classical formula holds for it; the point is the signs and the
normalisation of the named hypothesis `ResidueShift`, which this identity is equivalent to (`explicit_formula`).
Zeros from mpmath.zetazero (first N, both signs of gamma). CPU only, about a minute.
"""
import mpmath as mp

mp.mp.dps = 30
N_ZEROS = 200
C_LINE = 2


def H(s, a, sig):
    w = s - mp.mpf(1) / 2
    return sig * mp.sqrt(2 * mp.pi) * mp.exp(a * w + sig ** 2 * w ** 2 / 2)


def g(x, a, sig):
    return mp.exp(-(x - a) ** 2 / (2 * sig ** 2))


def von_mangoldt(n):
    for p in range(2, int(n ** 0.5) + 1):
        if n % p == 0:
            m = n
            while m % p == 0:
                m //= p
            return mp.log(p) if m == 1 else mp.mpf(0)
    return mp.log(n) if n > 1 else mp.mpf(0)


def prime_sum(a, sig, nmax):
    return mp.fsum(von_mangoldt(n) / mp.sqrt(n) * g(mp.log(n), a, sig) for n in range(2, nmax))


def arch(a, sig, c=C_LINE):
    f = lambda t: (mp.digamma((c + 1j * t) / 2) - mp.log(mp.pi)) * H(c + 1j * t, a, sig)
    return mp.quad(f, [-mp.inf, -20, 0, 20, mp.inf]) / (2 * mp.pi)


GAMMAS = [mp.im(mp.zetazero(k)) for k in range(1, N_ZEROS + 1)]


def zero_sum(a, sig):
    return mp.fsum(H(mp.mpf(1) / 2 + 1j * gm, a, sig) + H(mp.mpf(1) / 2 - 1j * gm, a, sig) for gm in GAMMAS)


def check(a, sig, nmax):
    lhs = zero_sum(a, sig)
    rhs = (H(1, a, sig) + H(0, a, sig) - (prime_sum(a, sig, nmax) + prime_sum(-a, sig, nmax))
           + (arch(a, sig) + arch(-a, sig)) / 2)
    return lhs, rhs


if __name__ == "__main__":
    print(f"explicit formula check: {N_ZEROS} zeros (gamma up to {mp.nstr(GAMMAS[-1], 6)}), line c = {C_LINE}")
    cases = [(0, 0.15, 50), (0, 0.5, 20000), (0.3, 0.5, 20000), (0.4, 0.3, 5000)]
    worst = 0
    for a, sig, nmax in cases:
        lhs, rhs = check(mp.mpf(a), mp.mpf(sig), nmax)
        err = abs(lhs - rhs)
        worst = max(worst, err)
        print(f"a={a:<4} sigma={sig:<5} zero side {mp.nstr(lhs, 12):>28}  right side {mp.nstr(rhs, 12):>28}"
              f"  |diff| {mp.nstr(err, 3)}")
    # control: flip the sign of the prime sum; the identity must fail visibly
    a, sig, nmax = mp.mpf(0), mp.mpf(0.5), 20000
    lhs = zero_sum(a, sig)
    bad = H(1, a, sig) + H(0, a, sig) + 2 * prime_sum(a, sig, nmax) + arch(a, sig)
    print(f"control (prime sign flipped), a=0 sigma=0.5: |diff| {mp.nstr(abs(lhs - bad), 3)}")
    print("PASS" if worst < 1e-8 else "FAIL")
