"""EXPLORATORY coarse-scale test of the near-cut set (COARSE-TEST.md, plan fixed before running). CPU only.

Usage: py coarse_test.py [--out runs/coarse_test.json]
"""
import argparse
import itertools
import json
import math

import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components

CONJ = np.array([1.0, -1.0, -1.0, -1.0])
W = 0.5
PLANES = [(m, n) for m in range(4) for n in range(m + 1, 4)]


def qm(a, b):
    a0, a1, a2, a3 = a[..., 0], a[..., 1], a[..., 2], a[..., 3]
    b0, b1, b2, b3 = b[..., 0], b[..., 1], b[..., 2], b[..., 3]
    return np.stack([a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3, a0 * b1 + b0 * a1 - (a2 * b3 - a3 * b2),
                     a0 * b2 + b0 * a2 - (a3 * b1 - a1 * b3), a0 * b3 + b0 * a3 - (a1 * b2 - a2 * b1)], axis=-1)


def sh(F, mu, k):
    """Field at x + k e_mu (periodic); F has site axes 0..3 and the quaternion axis last."""
    return np.roll(F, -k, axis=mu)


def block(U):
    """One step of the W2 good blocking, projected: U (4, L, L, L, L, 4) -> (4, L/2, ..., 4)."""
    out = []
    for mu in range(4):
        Um = U[mu]
        S = qm(Um, sh(Um, mu, 1))
        for nu in range(4):
            if nu == mu:
                continue
            Un = U[nu]
            # s = +1: U_nu(y) U_mu(y+nu) U_mu(y+nu+mu) U_nu(y+2mu)^dag
            a = qm(qm(qm(Un, sh(Um, nu, 1)), sh(sh(Um, nu, 1), mu, 1)), sh(Un, mu, 2) * CONJ)
            # s = -1: U_nu(y-nu)^dag U_mu(y-nu) U_mu(y-nu+mu) U_nu(y-nu+2mu)
            b = qm(qm(qm(sh(Un, nu, -1) * CONJ, sh(Um, nu, -1)), sh(sh(Um, nu, -1), mu, 1)), sh(sh(Un, nu, -1), mu, 2))
            S = S + W * (a + b)
        S = S / np.linalg.norm(S, axis=-1, keepdims=True)
        out.append(S[::2, ::2, ::2, ::2])
    return np.stack(out)


def plaquettes(U):
    """q0 of all plaquettes, shape (L, L, L, L, 6)."""
    q = []
    for (m, n) in PLANES:
        P = qm(qm(qm(U[m], sh(U[n], m, 1)), sh(U[m], n, 1) * CONJ), U[n] * CONJ)
        q.append(P[..., 0])
    return np.stack(q, axis=-1)


def clusters(near):
    """Clusters of near-cut plaquettes (faces of a common cube are adjacent), periodic. near: (L, L, L, L, 6) bool.
    Returns labels for near plaquettes (flat index), sizes, and spanning flag."""
    L = near.shape[0]
    idx = np.arange(near.size).reshape(near.shape)
    pidx = {pl: i for i, pl in enumerate(PLANES)}
    rows, cols = [], []
    for (a, b, c) in itertools.combinations(range(4), 3):
        faces = []
        for (p, q, r) in ((a, b, c), (a, c, b), (b, c, a)):
            k = pidx[(p, q)]
            faces.append(idx[..., k])                                  # face at x
            faces.append(np.roll(idx[..., k], -1, axis=r))              # face at x + e_r
        F = np.stack([f.ravel() for f in faces])                        # (6, L^4) plaquette indices per cube
        nf = near.ravel()[F]
        for i in range(6):
            for j in range(i + 1, 6):
                m = nf[i] & nf[j]
                rows.append(F[i][m])
                cols.append(F[j][m])
    r = np.concatenate(rows)
    c = np.concatenate(cols)
    n = near.size
    G = coo_matrix((np.ones(len(r)), (r, c)), shape=(n, n))
    ncomp, lab = connected_components(G, directed=False)
    nflat = near.ravel()
    labn = lab[nflat]
    if labn.size == 0:
        return np.array([], int), False, 0
    uniq, inv = np.unique(labn, return_inverse=True)
    sizes = np.bincount(inv)
    coords = np.stack(np.unravel_index(np.nonzero(nflat)[0], near.shape)[:4], axis=-1)
    span = False
    for d in range(4):
        key = np.unique(inv * L + coords[:, d])
        cnt = np.bincount(key // L, minlength=len(uniq))
        if np.any(cnt == L):
            span = True
            break
    return sizes, span, int(sizes.max())


def tail_fit(sizes):
    s = np.sort(np.asarray(sizes))
    if len(s) < 10:
        return dict(slope=None, r2=None)
    vals = np.arange(2, s.max() + 1)
    ccdf = np.array([np.mean(s >= v) for v in vals])
    ok = ccdf > 0
    x, y = vals[ok], np.log(ccdf[ok])
    if len(x) < 3:
        return dict(slope=None, r2=None, smax=int(s.max()))
    A = np.vstack([x, np.ones_like(x)]).T
    coef, res, *_ = np.linalg.lstsq(A, y, rcond=None)
    yhat = A @ coef
    r2 = 1 - np.sum((y - yhat) ** 2) / max(np.sum((y - y.mean()) ** 2), 1e-300)
    return dict(slope=float(coef[0]), r2=float(r2), smax=int(s.max()))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="runs/coarse_test.json")
    a = ap.parse_args()
    out = {}
    for beta in (2.3, 3.5):
        d = np.load(f"runs/conf_b{beta}.npz")
        confs = d["U"]                                                  # (n, 4, 16, 16, 16, 16, 4)
        # coarse configurations per factor, with offsets
        levels = {1: [], 2: [], 4: []}
        for ci in range(confs.shape[0]):
            U = confs[ci]
            levels[1].append((ci, U))
            for o in itertools.product((0, 1), repeat=4):
                Us = U
                for mu in range(4):
                    Us = np.roll(Us, -o[mu], axis=1 + mu)
                levels[2].append((ci, block(Us)))
            for o in itertools.product((0, 2), repeat=4):
                Us = U
                for mu in range(4):
                    Us = np.roll(Us, -o[mu], axis=1 + mu)
                levels[4].append((ci, block(block(Us))))
        q0s = {b: [(ci, plaquettes(Uc)) for ci, Uc in lst] for b, lst in levels.items()}
        mean = {b: float(np.mean([q.mean() for _, q in q0s[b]])) for b in q0s}
        res = {}
        for b in (1, 2, 4):
            beff = beta * (1 - mean[1]) / (1 - mean[b])
            dP = math.log(6) / (2 * beff)
            dP_fine = math.log(6) / (2 * beta)
            thr = {"dP_eff": dP, "dP_fine": dP_fine, "0.05": 0.05, "0.1": 0.1, "0.2": 0.2, "0.3": 0.3, "0.4": 0.4}
            rb = dict(mean_q0=mean[b], beta_eff=beff, thresholds={})
            for name, delta in thr.items():
                per = []
                sizes_all = []
                for ci, q in q0s[b]:
                    near = np.abs(q) < delta
                    sizes, span, mx = clusters(near)
                    sizes_all += list(sizes)
                    per.append((ci, float(near.mean()), mx / near.size, span))
                per_conf = {}
                for ci, fn, lf, sp in per:
                    per_conf.setdefault(ci, []).append((fn, lf, sp))
                span_c = [np.mean([x[2] for x in v]) for v in per_conf.values()]
                lf_c = [np.mean([x[1] for x in v]) for v in per_conf.values()]
                fn_c = [np.mean([x[0] for x in v]) for v in per_conf.values()]
                sf = float(np.mean(span_c))
                lf = float(np.mean(lf_c))
                fit = tail_fit(sizes_all)
                verdict = ("disappears" if (sf <= 0.1 and lf < 0.05) else "persists" if sf >= 0.9 else "partial")
                expo = (fit.get("slope") is not None and fit["slope"] < 0 and fit["r2"] >= 0.9 and sf <= 0.1)
                rb["thresholds"][name] = dict(delta=delta, frac_near=float(np.mean(fn_c)), largest_share=lf,
                                              largest_share_sd=float(np.std(lf_c, ddof=1)) if len(lf_c) > 1 else None,
                                              spanning_frac=sf, spanning_sd=float(np.std(span_c, ddof=1)) if len(span_c) > 1 else None,
                                              n_coarse=len(per), tail=fit, exponential_tail=bool(expo), verdict=verdict)
            res[str(b)] = rb
        out[str(beta)] = res
        for b in ("1", "2", "4"):
            t = res[b]["thresholds"]["dP_eff"]
            print(f"beta {beta} factor {b}: <q0> {res[b]['mean_q0']:.3f} beta_eff {res[b]['beta_eff']:.2f} delta_P {t['delta']:.3f} | "
                  f"near {t['frac_near']:.3f} largest {t['largest_share']:.4f} spanning {t['spanning_frac']:.2f} "
                  f"tail {t['tail']} -> {t['verdict']}{' (exp tail)' if t['exponential_tail'] else ''}", flush=True)
    json.dump(out, open(a.out, "w"), indent=1)


if __name__ == "__main__":
    main()
