# Exploratory (after the pre-registered primary run): tolerance sensitivity and torus-size dependence of Gamma(D)
# along a spatial direction for the linearised good blocking. Not pre-registered; reported as exploratory.
import sys, numpy as np
import condphoton as cp
M, l, w = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
qs, K, K0, H, H0, Cq = cp.bloch(M, l, w, [0])
ev, U = np.linalg.eigh(K)
for tol in (1e-12, 1e-10, 1e-8, 1e-6):
    keep = ev > tol * ev.max(axis=-1, keepdims=True)
    Uh = np.einsum('qmi,qm->qi', U.conj(), H[0])
    tq = (np.abs(Uh) ** 2 * np.where(keep, 1.0 / np.where(keep, ev, 1.0), 0.0)).sum(-1)
    tq[0] = 0.0
    out = []
    for D in range(M // 2 + 1):
        ph = np.exp(-1j * qs[:, 3] * D)
        c = np.real(np.sum(Cq[0] * ph)) / M ** 4
        out.append(c - np.real(np.sum(tq * ph)) / M ** 4)
    print(f"M={M} l={l} w={w} tol={tol:g} Gamma(D) dir3 (q=0 constraint omitted):", " ".join(f"{g:+.3e}" for g in out))
nz = np.array([e[e > 1e-10 * e.max()].min() / e.max() if e.max() > 0 else np.inf for e in ev])
print("smallest kept relative eigenvalue over q:", np.sort(nz)[:5])
