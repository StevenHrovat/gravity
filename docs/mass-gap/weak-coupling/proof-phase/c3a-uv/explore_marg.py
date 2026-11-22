# Exploratory: marginal conditional weight G(q3) = mean over (q0,q1,q2) of g(q), on a dense q3 grid, to locate the
# non-analyticity behind the slowly decaying, alternating spatial conditional correlation. Not pre-registered.
import sys, numpy as np
import condphoton as cp

def weights(qs, l, w, o=0, tol=1e-10):
    nsteps = int(round(np.log2(l)))
    ns = np.stack(np.meshgrid(*[np.arange(l)] * 4, indexing='ij'), -1).reshape(-1, 4) * cp.TWO_PI
    K = np.zeros((len(qs), 6, 6), complex); h = np.zeros((len(qs), 6), complex); c = np.zeros(len(qs))
    for n in ns:
        k = (qs + n) / l
        p2 = (4 * np.sin(k / 2) ** 2).sum(-1)
        wt = np.where(p2 > 1e-14, 1 / np.where(p2 > 1e-14, p2, 1), 0)
        S = cp.composite_symbol(k, w, nsteps)
        e = np.exp(1j * l * k)
        psi = np.stack([(e[:, m] - 1)[:, None] * S[:, nn, :] - (e[:, nn] - 1)[:, None] * S[:, m, :] for (m, nn) in cp.PLAQ], 1)
        a = cp.obs_symbol(k, l, o)
        K += np.einsum('qic,qjc,q->qij', psi, psi.conj(), wt)
        h += np.einsum('qic,qc,q->qi', psi, a.conj(), wt)
        c += (np.abs(a) ** 2).sum(-1) * wt
    K /= l**4; h /= l**4; c /= l**4
    ev, U = np.linalg.eigh(K)
    keep = ev > tol * ev.max(-1, keepdims=True)
    u = np.einsum('qmi,qm->qi', U.conj(), h)
    t = (np.abs(u) ** 2 * np.where(keep, 1 / np.where(keep, ev, 1), 0)).sum(-1)
    return c, c - t

if __name__ == "__main__":
  l, w, Mo = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
  g1 = (np.arange(Mo) + 0.5) * cp.TWO_PI / Mo          # shifted grid avoids q = 0 exactly
  Q = np.stack(np.meshgrid(g1, g1, g1, indexing='ij'), -1).reshape(-1, 3)
  for q3 in list(np.linspace(0, np.pi, 9)) + [np.pi - 0.02, np.pi - 0.01]:
      qs = np.concatenate([Q, np.full((len(Q), 1), q3)], 1)
      c, g = weights(qs, l, w)
      print(f"q3={q3:.4f}  mean c={c.mean():.6e}  mean g={g.mean():.6e}  min g={g.min():.3e}")
