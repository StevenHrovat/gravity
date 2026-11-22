# Exploratory: smallest non-gauge eigenvalue of the coarse flux covariance K(q) over the coarse zone (rank-3 part). Not pre-registered.
import sys, numpy as np, condphoton as cp
from explore_marg import weights
M, l, w = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
qs, K, K0, H, H0, Cq = cp.bloch(M, l, w, [0])
ev = np.linalg.eigvalsh(K)[:, 3]      # 4th eigenvalue = smallest of the rank-3 (gauge-invariant) part
ev[0] = np.inf
i = np.argsort(ev)[:5]
for j in i:
    print('q*M/2pi =', np.round(qs[j] * M / cp.TWO_PI, 2), 'lambda_min =', ev[j])
