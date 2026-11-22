# Exploratory: eigenvalues of the coarse flux covariance K(q) and observable overlaps near the zone corner. Not pre-registered.
import sys, numpy as np, condphoton as cp
l, w = int(sys.argv[1]), float(sys.argv[2])
nsteps = int(round(np.log2(l)))
ns = np.stack(np.meshgrid(*[np.arange(l)] * 4, indexing='ij'), -1).reshape(-1, 4) * cp.TWO_PI
P = np.pi
for eps in (0.0, 0.1, 0.01):
    q = np.array([P, P + eps, P, P])
    k = (q[None] + ns) / l
    p2 = (4 * np.sin(k / 2) ** 2).sum(-1); wt = 1 / p2
    S = cp.composite_symbol(k, w, nsteps); e = np.exp(1j * l * k)
    psi = np.stack([(e[:, m] - 1)[:, None] * S[:, n, :] - (e[:, n] - 1)[:, None] * S[:, m, :] for (m, n) in cp.PLAQ], 1)
    a = cp.obs_symbol(k, l, 0)
    K = np.einsum('aic,ajc,a->ij', psi, psi.conj(), wt) / l**4
    h = np.einsum('aic,ac,a->i', psi, a.conj(), wt) / l**4
    ev, U = np.linalg.eigh(K)
    print(f"eps={eps}: eig {np.array2string(ev, precision=5)}  |overlap|^2 {np.array2string(np.abs(U.conj().T @ h)**2, precision=6)}")
    if eps == 0.0:
        Sx = S[:, :, :]
        print('  composite symbol rank per alias:', [np.linalg.matrix_rank(s, tol=1e-9) for s in Sx][:16])
