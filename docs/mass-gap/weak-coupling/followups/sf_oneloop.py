"""Follow-up experiment 1 (route (d)): exact one-loop running of a free-energy box influence (Schroedinger-functional type).

Pre-registered in PREREG-FOLLOWUPS.md (Experiment 1). CPU only, one process, seconds to minutes.

Lattice L^3 x T (spatially periodic, time boundaries x0 = 0, T), spatial boundary links fixed to an abelian background
exp(i phi sigma3 / L), exp(i phi' sigma3 / L), phi = eta, phi' = pi - eta. Wilson action s = sum_p (1 - Re tr U_p / N).
One loop: Gamma_1 = 1/2 ln det(h + lam D D^T) - ln det(D^T D) (background gauge + ghosts), h = Hessian of s at the background,
D = infinitesimal gauge map at the sites 0 < x0 < T. beta_kappa = beta - Gamma_1'/s_cl' (eta = pi/4).

Usage: py sf_oneloop.py check            (consistency checks, real space vs momentum space)
       py sf_oneloop.py run L1 L2 ...    (writes sf_oneloop.json)
"""
import itertools
import json
import os
import sys
import time

os.environ.setdefault("CUDA_VISIBLE_DEVICES", "-1")
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
SIG = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]], complex), np.array([[1, 0], [0, -1]], complex)]
ETA0 = np.pi / 4
HSTEP = 1e-4


class Group:
    def __init__(self, name):
        self.name = name
        if name == "SU2":
            self.N = 2
            self.T = [1j * s / 2 for s in SIG]
        else:
            self.N = 1
            self.T = [np.array([[1j]])]
        self.ng = len(self.T)
        self.norm = [np.trace(t.conj().T @ t).real for t in self.T]

    def bg(self, theta):
        if self.name == "SU2":
            return np.diag([np.exp(1j * theta), np.exp(-1j * theta)])
        return np.array([[np.exp(1j * theta)]])

    def ad(self, V):
        R = np.zeros((self.ng, self.ng))
        Vi = V.conj().T
        for b in range(self.ng):
            M = V @ self.T[b] @ Vi
            for a in range(self.ng):
                R[a, b] = (np.trace(self.T[a].conj().T @ M) / self.norm[a]).real
        return R


def build(G, Ls, T, L, eta, origin_only=True):
    """Operators on an Ls^3 x (T+1) lattice (spatially periodic) carrying the background of the target size L x T.
    origin_only: only plaquettes containing a link at spatial site 0 (enough for the stencil rows at the origin).
    Returns links, sites, gradient, Hessian h (sparse), gauge map D (sparse), s_cl per spatial site."""
    import scipy.sparse as sp
    phi, phip = eta, np.pi - eta
    theta = lambda x0: (x0 * phip + (T - x0) * phi) / (L * T)
    I = np.eye(G.N, dtype=complex)

    def V(x0, mu):
        return I if mu == 0 else G.bg(theta(x0))

    def dynamic(x0, mu):
        return (0 <= x0 <= T - 1) if mu == 0 else (1 <= x0 <= T - 1)

    def exists(x0, mu):
        return (0 <= x0 <= T - 1) if mu == 0 else (0 <= x0 <= T)

    def shift(x, mu):
        y = list(x)
        y[mu] += 1
        if mu > 0:
            y[mu] %= Ls
        return tuple(y)

    links = [(x0,) + xs + (mu,) for x0 in range(T + 1) for xs in itertools.product(range(Ls), repeat=3)
             for mu in range(4) if dynamic(x0, mu)]
    lidx = {l: i for i, l in enumerate(links)}
    sites = [(x0,) + xs for x0 in range(1, T) for xs in itertools.product(range(Ls), repeat=3)]
    sidx = {s: i for i, s in enumerate(sites)}
    ng = G.ng
    n = len(links) * ng
    rows, cols, vals = [], [], []
    grad = np.zeros(n)
    s_cl = 0.0
    pos = [0, 2, 5, 7]
    sgn = [1, 1, -1, -1]
    TT = [[0.5 * (G.T[a] @ G.T[b] + G.T[b] @ G.T[a]) for b in range(ng)] for a in range(ng)]
    O = (0, 0, 0)
    for x0 in range(T + 1):
        for xs in itertools.product(range(Ls), repeat=3):
            x = (x0,) + xs
            for mu in range(4):
                for nu in range(mu + 1, 4):
                    L4 = [(x, mu), (shift(x, mu), nu), (shift(x, nu), mu), (x, nu)]
                    if not all(0 <= y[0] <= T and exists(y[0], m) for (y, m) in L4):
                        continue
                    if origin_only and not any(tuple(y[1:]) == O for (y, m) in L4):
                        continue
                    dyn = [dynamic(y[0], m) for (y, m) in L4]
                    if not any(dyn):
                        continue
                    Vs = [V(y[0], m) for (y, m) in L4]
                    fixed = [None, Vs[0], None, Vs[1], Vs[2].conj().T, None, Vs[3].conj().T, None]

                    def prod(ins):
                        M = I
                        for k in range(8):
                            if fixed[k] is not None:
                                M = M @ fixed[k]
                            elif k in ins:
                                M = M @ ins[k]
                        return M

                    if tuple(xs) == O or not origin_only:
                        s_cl += 1 - np.trace(prod({})).real / G.N
                    ids = [lidx[y + (m,)] if d else None for (y, m), d in zip(L4, dyn)]
                    for i in range(4):
                        if not dyn[i]:
                            continue
                        for a in range(ng):
                            ia = ids[i] * ng + a
                            grad[ia] += -np.trace(prod({pos[i]: sgn[i] * G.T[a]})).real / G.N
                            for j in range(4):
                                if not dyn[j]:
                                    continue
                                for b in range(ng):
                                    jb = ids[j] * ng + b
                                    if i == j:
                                        ins = {pos[i]: TT[a][b]}
                                    else:
                                        ins = {pos[i]: sgn[i] * G.T[a], pos[j]: sgn[j] * G.T[b]}
                                    rows.append(ia); cols.append(jb)
                                    vals.append(-np.trace(prod(ins)).real / G.N)
    h = sp.csr_matrix((vals, (rows, cols)), shape=(n, n))
    dr, dc, dv = [], [], []
    for i, l in enumerate(links):
        x, mu = l[:4], l[4]
        y = shift(x, mu)
        if x in sidx:
            for a in range(ng):
                dr.append(i * ng + a); dc.append(sidx[x] * ng + a); dv.append(1.0)
        if y in sidx:
            R = G.ad(V(x[0], mu))
            for a in range(ng):
                for b in range(ng):
                    if abs(R[a, b]) > 1e-15:
                        dr.append(i * ng + a); dc.append(sidx[y] * ng + b); dv.append(-R[a, b])
    D = sp.csr_matrix((dv, (dr, dc)), shape=(n, len(sites) * ng))
    if origin_only:
        s_cl_site = s_cl
    else:
        s_cl_site = s_cl / Ls ** 3
    orows = np.array([i * ng + a for i, l in enumerate(links) if tuple(l[1:4]) == O for a in range(ng)])
    return links, sites, grad[orows], h, D, s_cl_site, orows


def stencil(rows_items, cols_items, A, ng, Ls):
    """Bloch stencil of operator A (rows indexed by items with spatial coords in positions 1..3).
    Returns dict offset -> dense block (row local index at spatial origin, col local index)."""
    def local_key(it):
        return (it[0],) + tuple(it[4:])  # x0 and (mu) if link
    rloc = {}
    for it in rows_items:
        k = local_key(it)
        if k not in rloc:
            rloc[k] = len(rloc)
    cloc = {}
    for it in cols_items:
        k = local_key(it)
        if k not in cloc:
            cloc[k] = len(cloc)
    blocks = {}
    for ri, it in enumerate(rows_items):
        if tuple(it[1:4]) != (0, 0, 0):
            continue
        for a in range(ng):
            row = A.getrow(ri * ng + a)
            for c, val in zip(row.indices, row.data):
                if abs(val) < 1e-15:
                    continue
                cj, b = divmod(c, ng)
                jt = cols_items[cj]
                off = tuple(((v + Ls // 2) % Ls) - Ls // 2 for v in jt[1:4])
                assert all(abs(o) <= 1 for o in off), off
                if off not in blocks:
                    blocks[off] = np.zeros((len(rloc) * ng, len(cloc) * ng))
                blocks[off][rloc[local_key(it)] * ng + a, cloc[local_key(jt)] * ng + b] += val
    return blocks


def ops(G, T, L, eta, lam):
    Ls = 4
    links, sites, grad, h, D, s_cl, orows = build(G, Ls, T, L, eta)
    M = (h + lam * (D @ D.T)).tocsr()
    K = (D.T @ D).tocsr()
    hD = (h[orows] @ D)
    return dict(M=stencil(links, links, M, G.ng, Ls), K=stencil(sites, sites, K, G.ng, Ls),
                s_cl_per_site=s_cl, grad=np.abs(grad).max(), hD=abs(hD).max() if hD.nnz else 0.0)


def momenta(L, reduce):
    if not reduce:
        return [(n, 1) for n in itertools.product(range(L), repeat=3)]
    cls = {}
    for n in itertools.product(range(L), repeat=3):
        # symmetries of the blocks: permutations of the spatial axes and the global sign p -> -p (M(-p) = conj M(p));
        # single-axis reflections are NOT symmetries for the charged (background-coupled) components
        m = tuple((L - v) % L for v in n)
        key = min(tuple(sorted(n)), tuple(sorted(m)))
        cls[key] = cls.get(key, 0) + 1
    return list(cls.items())


def assemble(blocks, ps):
    offs = list(blocks.keys())
    B = np.stack([blocks[o] for o in offs])  # (no, d, d)
    O = np.array(offs, float)  # (no, 3)
    ph = np.exp(1j * ps @ O.T)  # (np, no)
    return np.einsum("po,oij->pij", ph, B)


def chol_logdet(M):
    C = np.linalg.cholesky(M)  # raises if not positive definite
    return 2 * np.log(np.abs(np.diagonal(C, axis1=1, axis2=2).real)).sum(1)


def logdet_deriv_fast(Mp, Mm):
    return (chol_logdet(Mp) - chol_logdet(Mm)) / (2 * HSTEP), np.zeros(len(Mp), int)


def logdet_deriv(Mp, Mm, zero_tol=1e-9):
    """d/deta ln det from blocks at eta+h, eta-h (batched). Uses eigenvalues (drops eta-independent zero modes)."""
    ep = np.linalg.eigvalsh(Mp)
    em = np.linalg.eigvalsh(Mm)
    scale = np.abs(ep).max(axis=1, keepdims=True)
    zp = np.abs(ep) < zero_tol * scale
    zm = np.abs(em) < zero_tol * scale
    if not np.array_equal(zp.sum(1), zm.sum(1)):
        raise RuntimeError("zero-mode count depends on eta")
    if (ep[~zp] < 0).any():
        raise RuntimeError("negative mode")
    lp = np.where(zp, 0.0, np.log(np.where(zp, 1.0, np.abs(ep)))).sum(1)
    lm = np.where(zm, 0.0, np.log(np.where(zm, 1.0, np.abs(em)))).sum(1)
    return (lp - lm) / (2 * HSTEP), zp.sum(1)


def gamma1_deriv(G, L, lam=1.0, reduce=None, batch=128):
    T = L
    op = ops(G, T, L, ETA0 + HSTEP, lam)
    om = ops(G, T, L, ETA0 - HSTEP, lam)
    if reduce is None:
        reduce = L > 12
    mlist = momenta(L, reduce)
    tot = 0.0
    nzero = 0
    for k in range(0, len(mlist), batch):
        chunk = mlist[k:k + batch]
        ps = 2 * np.pi * np.array([c[0] for c in chunk], float) / L
        w = np.array([c[1] for c in chunk], float)
        f = logdet_deriv if k == 0 else logdet_deriv_fast  # the zero momentum (first entry) carries the zero mode
        dM, z1 = f(assemble(op["M"], ps), assemble(om["M"], ps))
        dK, z2 = f(assemble(op["K"], ps), assemble(om["K"], ps))
        tot += (w * (0.5 * dM - dK)).sum()
        nzero += int((w * z1).sum() + (w * z2).sum())
    s_cl_p = (op["s_cl_per_site"] - om["s_cl_per_site"]) / (2 * HSTEP) * L ** 3
    return dict(G1p=tot, s_clp=s_cl_p, ratio=tot / s_cl_p, nzero=nzero, grad=max(op["grad"], om["grad"]),
                hD=max(op["hD"], om["hD"]))


def realspace_deriv(G, L, lam=1.0):
    """Direct computation on the full L^3 x T lattice (dense), for the check."""
    T = L
    vals = []
    for eta in (ETA0 + HSTEP, ETA0 - HSTEP):
        links, sites, grad, h, D, s_cl, orows = build(G, L, T, L, eta, origin_only=False)
        s_cl = s_cl * L ** 3
        M = (h + lam * (D @ D.T)).toarray()
        K = (D.T @ D).toarray()
        em = np.linalg.eigvalsh(M)
        ek = np.linalg.eigvalsh(K)
        sc = np.abs(em).max()
        em = em[np.abs(em) > 1e-9 * sc]
        vals.append((0.5 * np.log(em).sum() - np.log(ek).sum(), s_cl))
    return (vals[0][0] - vals[1][0]) / (2 * HSTEP), (vals[0][1] - vals[1][1]) / (2 * HSTEP)


def main():
    mode = sys.argv[1]
    if mode == "check":
        out = {}
        for gname in ("SU2", "U1"):
            G = Group(gname)
            for L in (3, 4):
                t0 = time.time()
                r = gamma1_deriv(G, L, reduce=False)
                r2 = gamma1_deriv(G, L, lam=2.0, reduce=False)
                rr = gamma1_deriv(G, L, reduce=True)
                g_rs, s_rs = realspace_deriv(G, L)
                line = dict(group=gname, L=L, G1p_mom=r["G1p"], G1p_lam2=r2["G1p"], G1p_reduced=rr["G1p"], G1p_real=g_rs,
                            s_clp_mom=r["s_clp"], s_clp_real=s_rs, grad=r["grad"], hD=r["hD"], nzero=r["nzero"],
                            secs=time.time() - t0)
                print(line, flush=True)
                out["%s_%d" % (gname, L)] = line
        json.dump(out, open(os.path.join(HERE, "sf_oneloop_check.json"), "w"), indent=1)
    else:
        Ls_ = [int(v) for v in sys.argv[2:]]
        path = os.path.join(HERE, "sf_oneloop.json")
        res = json.load(open(path)) if os.path.exists(path) else {}
        for gname in ("SU2", "U1"):
            G = Group(gname)
            for L in Ls_:
                t0 = time.time()
                r = gamma1_deriv(G, L)
                r["secs"] = time.time() - t0
                r["beta_minus_betakappa"] = r["ratio"]
                print(gname, L, r, flush=True)
                res["%s_%d" % (gname, L)] = r
                json.dump(res, open(path, "w"), indent=1)


if __name__ == "__main__":
    main()
