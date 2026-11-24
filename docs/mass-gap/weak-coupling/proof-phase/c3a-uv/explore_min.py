# Exploratory: locate the minimum of the conditional weight g(q) on the q3 = pi plane. Not pre-registered.
import sys, numpy as np, condphoton as cp
from explore_marg import weights
l, w, Mo = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
g1 = (np.arange(Mo) + 0.5) * cp.TWO_PI / Mo
Q = np.stack(np.meshgrid(g1, g1, g1, indexing='ij'), -1).reshape(-1, 3)
qs = np.concatenate([Q, np.full((len(Q), 1), np.pi)], 1)
c, g = weights(qs, l, w)
for i in np.argsort(g)[:6]:
    print('q =', np.round(qs[i], 3), 'c =', c[i], 'g =', g[i])
for eps in (0.2, 0.1, 0.05, 0.025):
    for qq in ([eps, 0, 0, np.pi], [0, eps, 0, np.pi], [0, 0, eps, np.pi], [eps, eps, eps, np.pi], [0,0,0,np.pi-eps]):
        c1, g1_ = weights(np.array([qq]), l, w)
        print('eps', eps, 'q', np.round(qq, 3), 'c', round(c1[0], 6), 'g', round(g1_[0], 6))
