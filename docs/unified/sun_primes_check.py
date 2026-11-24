"""SU(N) with primes as the base: CPU checks of the classical structure formalised in ProofPhase/General/SUNTwist*.lean.
Numerical, a third layer that can refute or guide, never establish. No lattice, no Monte Carlo.
  (1) Electric sectors are norms: for the tunnelling model of zn_tunnel_check.py (N nodes, circulant hopping), the matrix
      Z_{k-l} is positive semidefinite and Z_e = (1/N) sum_k omega^{-ek} Z_k >= 0 (the Lean theorem `ZFam.elec_nonneg` is
      the lattice version, by reflection positivity); and a non-PSD even sequence gives some Z_e < 0 (the check can fail).
  (2) CRT: Z_N = prod of Z_{p^a}; the DFT kernel factorises, omega_{mn}^j = omega_m^{b j} omega_n^{a j} for m a + n b = 1
      (`stdAddChar_crt`), so the DFT of Z_{mn} is a Kronecker product of those of Z_m and Z_n after relabelling.
  (3) Prime centres: every nonzero k generates Z_p; for composite N some nonzero k generates a proper sub-centre.
  (4) Dirichlet: for every nontrivial character chi mod p (p = 3, 5, 7, 11), sum_k omega^{-ek} chi(k) = chi^{-1}(-e) tau(chi)
      (`elec_dirichlet_prime`) and |tau(chi)|^2 = p.
  (5) Fourier matrix: F^2 = C, F^4 = 1, order 2 for N = 2 and 4 for N >= 3."""
from math import gcd
import numpy as np


def dft(N):
    w = np.exp(2j * np.pi / N)
    return np.array([[w ** (-(j * k)) for k in range(N)] for j in range(N)])  # e-th row: omega^{-e k}


def tunnel_Z(N, hops, T):
    X = np.roll(np.eye(N), 1, axis=0)
    H = np.zeros((N, N))
    for d, t in hops.items():
        H -= t * (np.linalg.matrix_power(X, d) + np.linalg.matrix_power(X, d).T)
    E, V = np.linalg.eigh(H)
    P = V @ np.diag(np.exp(-T * E)) @ V.T
    return np.array([np.trace(np.linalg.matrix_power(X, k) @ P) for k in range(N)]).real


print("== (1) electric sectors are norms (PSD of Z_{k-l})")
rng = np.random.default_rng(11)
for N in range(2, 12):
    hops = {d: float(rng.uniform(0.01, 0.3)) for d in range(1, N // 2 + 1)}
    Z = tunnel_Z(N, hops, float(rng.uniform(1.0, 6.0)))
    G = np.array([[Z[(k - l) % N] for l in range(N)] for k in range(N)])
    Ze = (dft(N) @ Z) / N
    ok = np.linalg.eigvalsh(G).min() > -1e-9 and np.allclose(Ze.imag, 0) and Ze.real.min() > -1e-12
    # the Gram eigenvalues are N * Z_e (circulant): the two statements are one
    same = np.allclose(np.sort(np.linalg.eigvalsh(G)), np.sort(N * Ze.real))
    print(f"N={N:2d}: Z_(k-l) PSD and Z_e >= 0: {ok}; eigenvalues of Z_(k-l) = N Z_e: {same}; "
          f"min Z_e/Z = {Ze.real.min() / Z[0]:.3e}")
Zbad = np.array([1.0, 0.9, -0.5, 0.9])  # even but not positive definite
print("    refutation test, an even sequence that is not a norm: Z_e =", np.round((dft(4) @ Zbad).real / 4, 4),
      "(some < 0, as it must be)")

print("\n== (2) CRT factorisation of the Fourier kernel")
for m, n in ((2, 3), (2, 5), (3, 4), (4, 9), (5, 11)):
    # integers a, b with m a + n b = 1
    a = pow(m, -1, n)  # m a = 1 mod n
    b = (1 - m * a) // n
    assert m * a + n * b == 1
    ok = all(np.isclose(np.exp(2j * np.pi * j / (m * n)),
                        np.exp(2j * np.pi * b * j / m) * np.exp(2j * np.pi * a * j / n)) for j in range(m * n))
    # DFT of Z_mn equals the Kronecker product of DFT(Z_m) and DFT(Z_n) after the CRT relabellings
    idx = [(j % m, j % n) for j in range(m * n)]
    Fmn = dft(m * n)
    Fm, Fn = dft(m), dft(n)
    K = np.array([[Fm[(b * e) % m, x[0]] * Fn[(a * e) % n, x[1]] for x in idx] for e in range(m * n)])
    print(f"m={m}, n={n}, a={a}, b={b}: kernel factorises {ok}; DFT_mn = (DFT_m x DFT_n) relabelled "
          f"{np.allclose(Fmn, K)}")

print("\n== (3) prime centres: does every nonzero sector generate Z_N?")
for N in range(2, 13):
    gens = [k for k in range(1, N) if gcd(k, N) == 1]
    proper = [k for k in range(1, N) if gcd(k, N) > 1]
    print(f"N={N:2d}: {'prime' if len(gens) == N - 1 else 'composite'}; generators {gens}; "
          f"nonzero sectors in proper sub-centres {proper}")

print("\n== (4) Dirichlet characters and Gauss sums")
for p in (3, 5, 7, 11):
    g = next(r for r in range(2, p) if all(pow(r, (p - 1) // q, p) != 1 for q in range(2, p) if (p - 1) % q == 0
                                           and all(q % s for s in range(2, q))))
    log = {pow(g, i, p): i for i in range(p - 1)}
    w = np.exp(2j * np.pi / p)
    worst, mods = 0.0, []
    for j in range(1, p - 1):  # nontrivial characters chi_j(g^i) = e^{2 pi i j i/(p-1)}
        chi = np.array([0] + [np.exp(2j * np.pi * j * log[k] / (p - 1)) for k in range(1, p)])
        tau = sum(chi[k] * w ** k for k in range(p))
        mods.append(abs(tau) ** 2)
        for e in range(p):
            lhs = sum(w ** (-(k * e)) * chi[k] for k in range(p))
            rhs = (np.conj(chi[(-e) % p]) if e % p else 0) * tau
            worst = max(worst, abs(lhs - rhs))
    print(f"p={p:2d}: generator {g}; {p - 2} nontrivial characters; max |F chi - chi^-1(-e) tau| = {worst:.1e}; "
          f"|tau|^2 = {sorted(set(float(x) for x in np.round(mods, 9)))}")

print("\n== (5) Fourier matrix F_jk = omega^{jk}/sqrt N")
for N in (2, 3, 4, 5, 6, 7, 11):
    F = np.conj(dft(N)) / np.sqrt(N)
    C = np.array([[1.0 if (j + k) % N == 0 else 0.0 for k in range(N)] for j in range(N)])
    order = next(r for r in (1, 2, 3, 4) if np.allclose(np.linalg.matrix_power(F, r), np.eye(N)))
    print(f"N={N:2d}: unitary {np.allclose(F @ F.conj().T, np.eye(N))}; F^2 = C {np.allclose(F @ F, C)}; "
          f"order {order} ({'half-turn' if order == 2 else 'quarter-turn'})")
