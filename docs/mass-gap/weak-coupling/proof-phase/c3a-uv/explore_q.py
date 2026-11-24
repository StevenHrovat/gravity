# Exploratory: conditional spectral weight g(q) = c(q) - h^+ K^+ h at single coarse momenta (linearised good blocking),
# to locate non-analyticities that produce power-law conditional correlations. Not pre-registered.
import sys, numpy as np
import condphoton as cp

def weight(q, l, w, o=0, tol=1e-10):
    nsteps = int(round(np.log2(l)))
    ns = np.stack(np.meshgrid(*[np.arange(l)] * 4, indexing='ij'), -1).reshape(-1, 4) * cp.TWO_PI
    k = (np.asarray(q)[None, :] + ns) / l
    p2 = (4 * np.sin(k / 2) ** 2).sum(-1)
    wt = np.where(p2 > 1e-14, 1 / np.where(p2 > 1e-14, p2, 1), 0)
    S = cp.composite_symbol(k, w, nsteps)
    e = np.exp(1j * l * k)
    psi = np.stack([(e[:, m] - 1)[:, None] * S[:, n, :] - (e[:, n] - 1)[:, None] * S[:, m, :] for (m, n) in cp.PLAQ], 1)
    a = cp.obs_symbol(k, l, o)
    K = np.einsum('aic,ajc,a->ij', psi, psi.conj(), wt) / l**4
    h = np.einsum('aic,ac,a->i', psi, a.conj(), wt) / l**4
    c = (np.abs(a)**2).sum(-1) @ wt / l**4
    ev, U = np.linalg.eigh(K)
    keep = ev > tol * ev.max()
    u = U.conj().T @ h
    return c, c - np.sum(np.abs(u[keep])**2 / ev[keep]), int(keep.sum()), ev

l, w = int(sys.argv[1]), float(sys.argv[2])
base = [float(v) for v in sys.argv[3].split(',')]   # q0,q1,q2 fixed
for q3 in np.linspace(np.pi - 0.4, np.pi + 0.4, 9):
    c, g, r, ev = weight(base + [q3], l, w)
    print(f"q=({base[0]:.2f},{base[1]:.2f},{base[2]:.2f},{q3:.3f}) rank {r} c={c:.5e} g={g:.5e} eig={np.round(ev, 5)}")
