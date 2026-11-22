# Exploratory: behaviour of the conditional weight g(q) near the coarse zone corner (pi,pi,pi,pi). Not pre-registered.
import sys, numpy as np
from explore_marg import weights
l, w = int(sys.argv[1]), float(sys.argv[2])
P = np.pi
dirs = {'t': [1, 0, 0, 0], 'x1': [0, 1, 0, 0], 'x3': [0, 0, 0, 1], 'diag': [1, 1, 1, 1], 'x1x2': [0, 1, 1, 0]}
c0, g0 = weights(np.array([[P, P, P, P]]), l, w)
print('corner: c', c0[0], 'g', g0[0])
for name, d in dirs.items():
    d = np.array(d, float) / np.linalg.norm(d)
    row = []
    for eps in (0.4, 0.2, 0.1, 0.05, 0.025):
        c, g = weights(np.array([[P, P, P, P]]) + eps * d[None, :], l, w)
        row.append(f"{g[0] - g0[0]:+.3e}")
    print(f"{name:5s} g-g(corner) at eps=0.4..0.025:", " ".join(row))
