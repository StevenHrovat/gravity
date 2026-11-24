"""Third-layer check for docs/unified/BLOWUP.md section 7 (Poincare and SU(N)). CPU, a few seconds. Needs numpy.

For SU(N) with the bi-invariant metric <X, Y> = -tr(XY) on su(N):
1. Orthonormal basis e_a, structure constants f_abc = <[e_a, e_b], e_c>.
2. Killing form B_ab = tr(ad e_a ad e_b); expected B = 2N tr(XY), i.e. B_ab = -2N delta_ab.
3. Ricci tensor of a bi-invariant metric, Ric_ab = (1/4) sum_cd f_acd f_bcd = -(1/4) B_ab; expected (N/2) delta_ab.
   Scalar curvature expected N (N^2 - 1)/2. Ricci flow g(t) = (1 - N t) g(0), extinction time 1/N (scalar ODE integrated).
4. Sectional curvature K(X, Y) = (1/4) |[X, Y]|^2 for orthonormal X, Y: all 1/2 for N = 2 (S^3 of radius sqrt 2);
   minimum 0 (flat planes, commuting diagonal X, Y) for N >= 3.
5. First nonzero eigenvalue of the Laplacian on functions: the Casimir of the fundamental representation,
   -sum_a e_a e_a = (N - 1/N) I (adjoint: N). Compared with Obata's bound n/(n-1) lambda and with 2 lambda
   (Cao-He's conformal instability window is n/(n-1) lambda < mu_1 < 2 lambda).
"""
import numpy as np


def basis(N):
    E = []
    for j in range(N):
        for k in range(j + 1, N):
            S = np.zeros((N, N), complex); S[j, k] = S[k, j] = 1
            A = np.zeros((N, N), complex); A[j, k] = 1; A[k, j] = -1
            E.append(1j * S); E.append(A)
    for m in range(1, N):
        D = np.zeros((N, N), complex)
        for j in range(m):
            D[j, j] = 1
        D[m, m] = -m
        E.append(1j * D)
    E = [X / np.sqrt(-np.trace(X @ X).real) for X in E]  # normalise to <X, X> = -tr(X X) = 1
    return E


def ip(X, Y):
    return -np.trace(X @ Y).real


def check(N):
    E = basis(N)
    n = len(E)
    G = np.array([[ip(X, Y) for Y in E] for X in E])
    orth = np.abs(G - np.eye(n)).max()
    f = np.zeros((n, n, n))
    for a in range(n):
        for b in range(a + 1, n):
            C = E[a] @ E[b] - E[b] @ E[a]
            for c in range(n):
                v = ip(C, E[c])
                f[a, b, c] = v
                f[b, a, c] = -v
    B = np.einsum("acd,bdc->ab", f, f)  # tr(ad e_a ad e_b) = sum_cd f_acd f_bdc
    Ric = 0.25 * np.einsum("acd,bcd->ab", f, f)
    lam = N / 2
    errB = np.abs(B + 2 * N * np.eye(n)).max()
    errR = np.abs(Ric - lam * np.eye(n)).max()
    scal = np.trace(Ric)
    # Ricci flow of the homothety factor: phi' = -2 lam (Ric is scale invariant), phi(0) = 1
    dt, phi, t = 1e-6, 1.0, 0.0
    while phi > 0:
        phi -= 2 * lam * dt
        t += dt
    # sectional curvatures
    rng = np.random.default_rng(N)
    Ks = []
    for _ in range(200):
        x, y = rng.normal(size=n), rng.normal(size=n)
        x /= np.linalg.norm(x); y -= (y @ x) * x; y /= np.linalg.norm(y)
        X = sum(xi * e for xi, e in zip(x, E)); Y = sum(yi * e for yi, e in zip(y, E))
        C = X @ Y - Y @ X
        Ks.append(0.25 * ip(C, C))
    Kflat = None
    if N >= 3:
        X, Y = E[-1], E[-2]  # two diagonal (Cartan) elements: they commute
        C = X @ Y - Y @ X
        Kflat = abs(0.25 * ip(C, C))
    cas_f = -sum(e @ e for e in E)
    mu1 = cas_f[0, 0].real
    cas_err = np.abs(cas_f - mu1 * np.eye(N)).max()
    obata = n / (n - 1) * lam
    print(f"N = {N:2d}: dim {n:3d}, orthonormality err {orth:.1e}; Killing = -2N delta err {errB:.1e}; "
          f"Ric = (N/2) delta err {errR:.1e}")
    print(f"        scalar {scal:.6f} (expected N(N^2-1)/2 = {N*(N*N-1)/2:.6f}); extinction t = {t:.5f} "
          f"(expected 1/N = {1/N:.5f})")
    print(f"        sectional K random: min {min(Ks):.4f} max {max(Ks):.4f}" +
          (f"; commuting Cartan pair K = {Kflat:.2e}" if Kflat is not None else "; all equal to 1/2"))
    print(f"        mu_1 = Casimir(fund) = {mu1:.6f} (N - 1/N = {N - 1/N:.6f}, err {cas_err:.1e}); "
          f"Obata n/(n-1) lambda = {obata:.6f}; 2 lambda = {2*lam:.6f}; "
          f"{'unstable window' if obata < mu1 - 1e-12 and mu1 < 2 * lam else 'edge (sphere)' if abs(mu1 - obata) < 1e-9 else 'outside'}")


if __name__ == "__main__":
    for N in (2, 3, 5, 11):
        check(N)
