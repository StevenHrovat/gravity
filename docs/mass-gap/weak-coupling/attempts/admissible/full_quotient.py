"""Companion to gaussian_gds.py: the same Gaussian influence, but measured modulo the gauge group of ALL sites of the cube
(interior and boundary sites), i.e. on test functions that are invariant also under boundary-site gauge rotations.
This is NOT the coefficient Theorem A uses (PROOF-NOTE §10.2: no step may use absolutely gauge-invariant influences); it
only shows how much of gamma_0 is boundary-gauge (open lines across the box) and how much is field strength.
Usage: py full_quotient.py d lmax"""
import itertools, sys, time
import numpy as np, scipy.sparse as sp, scipy.sparse.linalg as spla
import gaussian_gds as g

def run(d, l):
    t0 = time.time()
    V, shell, DV, DS, G, interior, dangling = g.build(d, l)
    M = (DV.T @ DV + G @ G.T).tocsc(); lu = spla.splu(M)
    sites = list(itertools.product(range(l + 1), repeat=d)); S = {x: i for i, x in enumerate(sites)}
    r_, c_, v_ = [], [], []
    for i, (x, mu) in enumerate(V):
        y = tuple(x[j] + (1 if j == mu else 0) for j in range(d))
        r_ += [i, i]; c_ += [S[y], S[x]]; v_ += [1.0, -1.0]
    Gf = sp.csr_matrix((v_, (r_, c_)), shape=(len(V), len(sites)))
    classes = {}
    for e in shell:
        classes.setdefault(g.canon(e, d, l), []).append(e)
    tot = 0.0
    for key, members in classes.items():
        j = shell.index(members[0])
        r = lu.solve(-(DV.T @ DS[:, j]).toarray().ravel())
        tot += len(members) * g.quotient_l1(r, Gf, len(sites))
    return tot / len(V), time.time() - t0

if __name__ == "__main__":
    d = int(sys.argv[1]); lmax = int(sys.argv[2])
    for l in range(2, lmax + 1):
        gam, s = run(d, l)
        print("d=%d l=%d gamma_full=%.4f (%.1fs)" % (d, l, gam, s), flush=True)
