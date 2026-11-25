"""Gaussian (free-field) value of the GDS coefficient for thin cubes: the 'photon value' gamma_0(l).

Route (c), attempt round 2026-11-21. Small CPU computation (no GPU).

Model: non-compact U(1) lattice gauge field on Z^d, action (1/2) sum_p (dA)_p^2 (the beta -> infinity Gaussian limit of
compact U(1), and, colour by colour, of SU(n) around the trivial background). Block V = thin cube of side l (links with both
ends in {0..l}^d). Given the shell values eta, the interior law is Gaussian with eta-independent covariance and mean
r(eta) = classical solution; a unit change of the shell link y shifts the mean by r^(y). The W-influence coefficient
(PROOF-NOTE §1.6, with per-link Lipschitz test functions; alignment Lemma 3.3/3.4) of y is then exactly the quotient l1 norm
    k_0(y) = min over interior gauge chi of sum_{e in V} |r^(y)_e + (d chi)_e|,
an LP. gamma_0(l) = sum_{y in shell} k_0(y) / |V| (per-direction form, by hypercubic symmetry), and gamma_0*(l) the same
without the dangling links (GDS*, PROOF-NOTE §3.7).

For compact U(1) or SU(n) at weak coupling with cold boundary condition, liminf_{beta->inf} k_beta(y) >= k_0(y) (Laplace
method at fixed l), so gamma_0(l) >= 1 means GDS fails at weak coupling on boxes of side l.

Usage: py gaussian_gds.py d lmax
"""
import itertools
import sys
import time

import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spla
from scipy.optimize import linprog


def build(d, l):
    def links_at(x):
        out = []
        for mu in range(d):
            out.append((tuple(x), mu))
            y = list(x); y[mu] -= 1
            out.append((tuple(y), mu))
        return out

    inC = lambda x: all(0 <= c <= l for c in x)
    V = []
    for x in itertools.product(range(l + 1), repeat=d):
        for mu in range(d):
            y = list(x); y[mu] += 1
            if inC(y):
                V.append((x, mu))
    Vidx = {e: i for i, e in enumerate(V)}
    # plaquettes touching V
    plaqs = set()
    for (x, mu) in V:
        for nu in range(d):
            if nu == mu:
                continue
            a, b = min(mu, nu), max(mu, nu)
            # the link (x,mu) is in plaquettes based at x and at x - e_nu
            for base in (x, tuple(x[i] - (1 if i == nu else 0) for i in range(d))):
                plaqs.add((base, a, b))
    plaqs = sorted(plaqs)

    def plaq_links(p):
        x, a, b = p
        xa = tuple(x[i] + (1 if i == a else 0) for i in range(d))
        xb = tuple(x[i] + (1 if i == b else 0) for i in range(d))
        return [((x, a), 1), ((xa, b), 1), ((xb, a), -1), ((x, b), -1)]

    shell = []
    for p in plaqs:
        for e, _ in plaq_links(p):
            if e not in Vidx:
                shell.append(e)
    shell = sorted(set(shell))
    Sidx = {e: i for i, e in enumerate(shell)}
    rows, cols, vals, srows, scols, svals = [], [], [], [], [], []
    for k, p in enumerate(plaqs):
        for e, s in plaq_links(p):
            if e in Vidx:
                rows.append(k); cols.append(Vidx[e]); vals.append(s)
            else:
                srows.append(k); scols.append(Sidx[e]); svals.append(s)
    DV = sp.csr_matrix((vals, (rows, cols)), shape=(len(plaqs), len(V)))
    DS = sp.csr_matrix((svals, (srows, scols)), shape=(len(plaqs), len(shell)))
    interior = [x for x in itertools.product(range(1, l), repeat=d)]
    Iidx = {x: i for i, x in enumerate(interior)}
    gr, gc, gv = [], [], []
    for i, (x, mu) in enumerate(V):
        y = tuple(x[j] + (1 if j == mu else 0) for j in range(d))
        if y in Iidx:
            gr.append(i); gc.append(Iidx[y]); gv.append(1.0)
        if x in Iidx:
            gr.append(i); gc.append(Iidx[x]); gv.append(-1.0)
    G = sp.csr_matrix((gv, (gr, gc)), shape=(len(V), max(len(interior), 1)))
    # dangling shell links: an endpoint whose other 2d-1 links are all in V
    dangling = set()
    for (x, mu) in shell:
        y = tuple(x[j] + (1 if j == mu else 0) for j in range(d))
        for s in (x, y):
            others = [e for e in links_at(s) if e != (x, mu)]
            if all(e in Vidx for e in others):
                dangling.add((x, mu))
    return V, shell, DV, DS, G, interior, dangling


def canon(e, d, l):
    x, mu = e
    m = [2 * x[i] + (1 if i == mu else 0) for i in range(d)]
    best = None
    for perm in itertools.permutations(range(d)):
        for flips in itertools.product((0, 1), repeat=d):
            t = tuple((2 * l - m[perm[i]]) if flips[i] else m[perm[i]] for i in range(d))
            if best is None or t < best:
                best = t
    return best


def quotient_l1(r, G, nint):
    nV = len(r)
    if nint == 0:
        return float(np.abs(r).sum())
    # variables: chi (nint), t (nV); minimise sum t, -t <= r + G chi <= t
    c = np.concatenate([np.zeros(nint), np.ones(nV)])
    I = sp.identity(nV, format="csr")
    A = sp.vstack([sp.hstack([G, -I]), sp.hstack([-G, -I])], format="csr")
    b = np.concatenate([-r, r])
    bounds = [(None, None)] * nint + [(0, None)] * nV
    res = linprog(c, A_ub=A, b_ub=b, bounds=bounds, method="highs")
    assert res.status == 0, res.message
    return res.fun


def run(d, l):
    t0 = time.time()
    V, shell, DV, DS, G, interior, dangling = build(d, l)
    nint = len(interior)
    M = (DV.T @ DV + G @ G.T).tocsc()
    lu = spla.splu(M)
    classes = {}
    for e in shell:
        classes.setdefault(canon(e, d, l), []).append(e)
    tot, tot_star, kmax = 0.0, 0.0, 0.0
    for key, members in classes.items():
        y = members[0]
        j = shell.index(y)
        rhs = -(DV.T @ DS[:, j]).toarray().ravel()
        r = lu.solve(rhs)
        k = quotient_l1(r, G, nint)
        mult = len(members)
        tot += mult * k
        if y not in dangling:
            tot_star += mult * k
        kmax = max(kmax, k)
        if DETAIL:
            print("   class %s mult=%d dangling=%s k=%.4f" % (key, mult, y in dangling, k))
    nV = len(V)
    return dict(d=d, l=l, nV=nV, nshell=len(shell), nclass=len(classes), gamma=tot / nV, gamma_star=tot_star / nV,
                kmax=kmax, secs=time.time() - t0)


DETAIL = False

if __name__ == "__main__":
    d = int(sys.argv[1]); lmax = int(sys.argv[2])
    lmin = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    DETAIL = len(sys.argv) > 4
    for l in range(lmin, lmax + 1):
        out = run(d, l)
        print("d=%(d)d l=%(l)d |V|=%(nV)d |shell|=%(nshell)d classes=%(nclass)d  gamma0=%(gamma).4f  gamma0*=%(gamma_star).4f"
              "  kmax=%(kmax).3f  (%(secs).1fs)" % out, flush=True)
