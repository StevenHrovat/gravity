"""The tunnelling identity for the centre Z_N of SU(N).
N nodes (the centre sectors), a Z_N-invariant tunnelling Hamiltonian H (circulant, nonnegative hopping), Euclidean time T.
Twisted traces Z_k = tr(X^k e^{-TH}), X the cyclic shift (twist by the centre element omega^k). Electric sectors are the
Z_N Fourier transform: Z_e = (1/N) sum_k omega^{-e k} Z_k. Checks:
  (1) Z_e / Z_0 = e^{-T (E_e - E_0)} exactly, E_e the eigenvalues of H (the gaps created by tunnelling);
  (2) bounds: Z_k real, 0 < Z_k < Z_0-twist (= Z) for k != 0, Z_k = Z_{N-k} (conjugation pairs k and N - k);
  (3) the Fourier matrix F is unitary with F^2 = C (k -> -k, conjugation) and F^4 = 1: for N = 2, C = 1 and F is the
      half-turn (Hadamard); for N >= 3, F is a quarter-turn whose square is the N-ality pairing;
  (4) N = 2 reproduces elec(c) = (1 - c)/(1 + c) = e^{-T gap}."""
import numpy as np


def run(N, hops, T):
    w = np.exp(2j * np.pi / N)
    X = np.roll(np.eye(N), 1, axis=0)
    H = np.zeros((N, N))
    for d, t in hops.items():
        H -= t * (np.linalg.matrix_power(X, d) + np.linalg.matrix_power(X, d).T)
    E, V = np.linalg.eigh(H)
    P = V @ np.diag(np.exp(-T * E)) @ V.T
    Zk = np.array([np.trace(np.linalg.matrix_power(X, k) @ P) for k in range(N)])
    Ze = np.array([sum(w ** (-e * k) * Zk[k] for k in range(N)) / N for e in range(N)]).real
    # eigenvalue of H on the Fourier mode e: E_e = -sum_d 2 t_d cos(2 pi d e / N)
    Ee = np.array([-sum(2 * t * np.cos(2 * np.pi * d * e / N) for d, t in hops.items()) for e in range(N)])
    ok1 = np.allclose(Ze / Ze[0], np.exp(-T * (Ee - Ee[0])))
    ok2 = (np.allclose(Zk.imag, 0) and all(0 < Zk[k].real < Zk[0].real for k in range(1, N))
           and all(np.isclose(Zk[k], Zk[N - k]) for k in range(1, N)))
    F = np.array([[w ** (j * k) for k in range(N)] for j in range(N)]) / np.sqrt(N)
    C = np.array([[1.0 if (j + k) % N == 0 else 0.0 for k in range(N)] for j in range(N)])
    ok3 = (np.allclose(F @ F.conj().T, np.eye(N)) and np.allclose(F @ F, C)
           and np.allclose(np.linalg.matrix_power(F, 4), np.eye(N)))
    order = 2 if np.allclose(F @ F, np.eye(N)) else 4
    print(f"N={N} hops={hops} T={T}: Z_e/Z_0 = e^(-T gap) {ok1}; 0 < Z_k < Z, Z_k = Z_(N-k) {ok2}; "
          f"F unitary, F^2 = conjugation, F^4 = 1 {ok3} (order {order})")
    print("    c_k = Z_k/Z:", np.round(Zk.real / Zk[0].real, 6), "  gaps E_e - E_0:", np.round(Ee - Ee[0], 6))
    if N == 2:
        c = Zk[1].real / Zk[0].real
        print(f"    N=2: elec(c) = {(1 - c) / (1 + c):.9f}, e^(-T gap) = {np.exp(-T * (Ee[1] - Ee[0])):.9f}")


for N, hops, T in ((2, {1: 0.3}, 4.0), (3, {1: 0.3}, 4.0), (4, {1: 0.2, 2: 0.05}, 3.0), (5, {1: 0.1, 2: 0.03}, 6.0),
                   (6, {1: 0.25}, 2.0), (8, {1: 0.15, 3: 0.02}, 5.0)):
    run(N, hops, T)

# The owner's candidates SU(5) and SU(11), with every N in between as tests, each with a generic nonnegative hopping.
print("\n== N = 5 to 11, generic hoppings (fixed seed)")
rng = np.random.default_rng(5)
for N in range(5, 12):
    hops = {d: round(float(rng.uniform(0.01, 0.3)), 3) for d in range(1, N // 2 + 1)}
    run(N, hops, round(float(rng.uniform(1.0, 6.0)), 2))
    divisors = [m for m in range(2, N) if N % m == 0]
    print(f"    centre Z_{N}: {'prime, no proper sub-centre' if not divisors else 'sub-centres Z_m for m in ' + str(divisors)}")
