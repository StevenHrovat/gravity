"""Conditional photon given the block field (c3a-uv, pre-registered in PREREG.md).

Linearised abelian gauge field on (Z/N)^4, N = M*l, Gaussian, covariance delta/phat^2 (Feynman gauge, constant mode removed).
Block field: linearised RouteA.goodBlocking (slice smearing with spatial staples, weight w; w = 0 is decimation), n = log2 l steps.
Conditioning on all coarse plaquette fluxes and the coarse zero-momentum link sums. Observable: F_12 averaged over a fine
hypercube of side l/2 (corner or centred in the cell); partner translated by D cells in time (dir 0) or space (dir 3).

Usage:  py condphoton.py check            (dense brute force vs Bloch on tiny tori)
        py condphoton.py run M l1,l2,... w1,w2,...  [--out file.json]
"""
import sys, json, time
import numpy as np

TWO_PI = 2 * np.pi
SPATIAL = (1, 2, 3)


def transverse(mu):
    return [nu for nu in SPATIAL if nu != mu]


# ---------------------------------------------------------------- symbols (momentum space)

def step_symbol(k, w):
    """Single smeared step at unit fine spacing: (..., 4) momenta -> (..., 4, 4) symbol, rows coarse dir, cols component."""
    sh = k.shape[:-1]
    s = np.zeros(sh + (4, 4), dtype=complex)
    for mu in range(4):
        T = transverse(mu)
        norm = 1.0 + w * 2 * len(T)
        em = np.exp(1j * k[..., mu])
        s[..., mu, mu] = (1 + em) * (1 + w * sum(2 * np.cos(k[..., nu]) for nu in T)) / norm
        for nu in T:
            s[..., mu, nu] = w * (1 - em ** 2) * (1 - np.exp(-1j * k[..., nu])) / norm
    return s


def composite_symbol(k, w, nsteps):
    S = np.broadcast_to(np.eye(4, dtype=complex), k.shape[:-1] + (4, 4)).copy()
    for i in range(nsteps):
        S = np.einsum('...ab,...bc->...ac', step_symbol(k * (2 ** i), w), S)
    return S


PLAQ = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


def obs_symbol(k, l, offset):
    """F_12 averaged over the fine box [offset, offset+b)^4, b = max(l//2, 1): (..., 4)."""
    b = max(l // 2, 1)
    box = np.ones(k.shape[:-1], dtype=complex)
    for mu in range(4):
        j = np.arange(offset, offset + b)
        box *= np.exp(1j * k[..., mu, None] * j).sum(-1) / b
    a = np.zeros(k.shape[:-1] + (4,), dtype=complex)
    a[..., 2] = (np.exp(1j * k[..., 1]) - 1) * box
    a[..., 1] = -(np.exp(1j * k[..., 2]) - 1) * box
    return a


def bloch(M, l, w, offsets, chunk=200000):
    """Return per coarse momentum q: K(q) (6x6 or 4x4 at q=0), hhat[offset](q), c[offset](q)."""
    nsteps = int(round(np.log2(l)))
    assert 2 ** nsteps == l
    qs = np.stack(np.meshgrid(*[np.arange(M)] * 4, indexing='ij'), -1).reshape(-1, 4) * TWO_PI / M
    ns = np.stack(np.meshgrid(*[np.arange(l)] * 4, indexing='ij'), -1).reshape(-1, 4) * TWO_PI
    nq = len(qs)
    K = np.zeros((nq, 6, 6), dtype=complex)
    K0 = np.zeros((4, 4), dtype=complex)
    H = {o: np.zeros((nq, 6), dtype=complex) for o in offsets}
    H0 = {o: np.zeros(4, dtype=complex) for o in offsets}
    Cq = {o: np.zeros(nq) for o in offsets}
    per = max(1, chunk // nq)
    for start in range(0, len(ns), per):
        nn = ns[start:start + per]
        k = (qs[None, :, :] + nn[:, None, :]) / l          # (a, q, 4)
        p2 = (4 * np.sin(k / 2) ** 2).sum(-1)
        wt = np.where(p2 > 1e-14, 1.0 / np.where(p2 > 1e-14, p2, 1.0), 0.0)
        S = composite_symbol(k, w, nsteps)                  # (a, q, 4, 4)
        e = np.exp(1j * l * k)                              # e^{i l k_mu} = e^{i q_mu}
        psi = np.stack([(e[..., m] - 1)[..., None] * S[..., n, :] - (e[..., n] - 1)[..., None] * S[..., m, :]
                        for (m, n) in PLAQ], -2)            # (a, q, 6, 4)
        K += np.einsum('aqic,aqjc,aq->qij', psi, psi.conj(), wt)
        K0 += np.einsum('aic,ajc,a->ij', S[:, 0], S[:, 0].conj(), wt[:, 0])
        for o in offsets:
            av = obs_symbol(k, l, o)
            H[o] += np.einsum('aqic,aqc,aq->qi', psi, av.conj(), wt)
            H0[o] += np.einsum('aic,ac,a->i', S[:, 0], av[:, 0].conj(), wt[:, 0])
            Cq[o] += ((np.abs(av) ** 2).sum(-1) * wt).sum(0)
    L4 = float(l) ** 4
    return qs, K / L4, K0 / L4, {o: H[o] / L4 for o in offsets}, {o: H0[o] / L4 for o in offsets}, \
        {o: Cq[o] / L4 for o in offsets}


def pinv_quad(Kq, h, tol=1e-10):
    """h^dagger K^+ h for a batch: Kq (q, m, m), h (q, m) -> (q,) complex, as quadratic form vectors."""
    ev, U = np.linalg.eigh(Kq)
    keep = ev > tol * ev.max(axis=-1, keepdims=True)
    inv = np.where(keep, 1.0 / np.where(keep, ev, 1.0), 0.0)
    Uh = np.einsum('qmi,qm->qi', U.conj(), h)
    return Uh, inv


def conditional(M, l, w, dirs=(0, 3), Dmax=None, offsets=None):
    if offsets is None:
        offsets = {'corner': 0, 'centre': l // 4}
    if Dmax is None:
        Dmax = M // 2
    qs, K, K0, H, H0, Cq = bloch(M, l, w, sorted(set(offsets.values())))
    res = {}
    for name, o in offsets.items():
        Uh, inv = pinv_quad(K, H[o])
        # q = 0 handled with the 4 zero-mode sums
        iq0 = 0
        ev0, U0 = np.linalg.eigh(K0)
        keep0 = ev0 > 1e-10 * ev0.max()
        u0 = U0.conj().T @ H0[o]
        t0 = np.sum(np.abs(u0[keep0]) ** 2 / ev0[keep0])
        tq = np.sum(np.abs(Uh) ** 2 * inv, axis=-1)
        tq[iq0] = t0
        out = {}
        for d in dirs:
            C, G = [], []
            for D in range(Dmax + 1):
                ph = np.exp(-1j * qs[:, d] * D)
                c = np.real(np.sum(Cq[o] * ph)) / M ** 4
                t = np.real(np.sum(tq * ph)) / M ** 4
                C.append(c)
                G.append(c - t)
            out[d] = {'C': C, 'Gamma': G, 'R': [g / c for g, c in zip(G, C)], 'kappa': 1 - G[0] / C[0]}
        res[name] = out
    return res


# ---------------------------------------------------------------- dense brute force (independent real-space construction)

def shift(arr, offs):
    """arr[..., x] -> arr[..., x + offs] on the last four axes."""
    return np.roll(arr, shift=[-o for o in offs], axis=(-4, -3, -2, -1))


def path_sum(A, steps):
    """Linear (abelian) transport along a path from every site: A (B, 4, N,N,N,N)."""
    pos = [0, 0, 0, 0]
    tot = np.zeros(A.shape[:1] + A.shape[2:])
    for (nu, fwd) in steps:
        if fwd:
            tot += shift(A[:, nu], pos)
            pos[nu] += 1
        else:
            pos[nu] -= 1
            tot -= shift(A[:, nu], pos)
    return tot


def real_step(A, w):
    """One smeared step in real space: (B, 4, 2M,...) -> (B, 4, M,...)."""
    out = []
    for mu in range(4):
        T = transverse(mu)
        acc = path_sum(A, [(mu, True), (mu, True)])
        for nu in T:
            for b in (True, False):
                acc = acc + w * path_sum(A, [(nu, b), (mu, True), (mu, True), (nu, not b)])
        acc = acc / (1 + w * 2 * len(T))
        out.append(acc[:, ::2, ::2, ::2, ::2])
    return np.stack(out, 1)


def real_constraints(A, w, nsteps):
    V = A
    for _ in range(nsteps):
        V = real_step(V, w)
    rows = []
    for (m, n) in PLAQ:
        rows.append((shift(V[:, n], [1 if i == m else 0 for i in range(4)]) - V[:, n]
                     - shift(V[:, m], [1 if i == n else 0 for i in range(4)]) + V[:, m]).reshape(V.shape[0], -1))
    rows.append(V.reshape(V.shape[0], 4, -1).sum(-1))
    return np.concatenate(rows, 1)


def real_obs(N, l, offset, D=0, d=0):
    b = max(l // 2, 1)
    a = np.zeros((4, N, N, N, N))
    for x in np.ndindex(b, b, b, b):
        s = [offset + xi for xi in x]
        s[d] += D * l
        e1 = list(s); e1[1] += 1
        e2 = list(s); e2[2] += 1
        idx = lambda v: tuple(c % N for c in v)
        a[(2,) + idx(e1)] += 1; a[(2,) + idx(s)] -= 1
        a[(1,) + idx(e2)] -= 1; a[(1,) + idx(s)] += 1
    return a / b ** 4


def apply_cov(v):
    """C v for v (B, 4, N,N,N,N): Feynman-gauge propagator, constant mode removed."""
    N = v.shape[-1]
    k = TWO_PI * np.arange(N) / N
    kk = np.meshgrid(k, k, k, k, indexing='ij')
    p2 = sum(4 * np.sin(x / 2) ** 2 for x in kk)
    inv = np.where(p2 > 1e-14, 1.0 / np.where(p2 > 1e-14, p2, 1.0), 0.0)
    return np.real(np.fft.ifftn(np.fft.fftn(v, axes=(-4, -3, -2, -1)) * inv, axes=(-4, -3, -2, -1)))


def brute_setup(M, l, w):
    N = M * l
    nsteps = int(round(np.log2(l)))
    dof = 4 * N ** 4
    P = []
    eye_chunk = 1024
    for s in range(0, dof, eye_chunk):
        idx = np.arange(s, min(dof, s + eye_chunk))
        E = np.zeros((len(idx), dof)); E[np.arange(len(idx)), idx] = 1
        P.append(real_constraints(E.reshape(-1, 4, N, N, N, N), w, nsteps))
    P = np.concatenate(P, 0).T                       # (constraints, dof)
    CP = apply_cov(P.reshape(-1, 4, N, N, N, N)).reshape(P.shape[0], -1)
    Kinv = np.linalg.pinv(P @ CP.T, rcond=1e-10, hermitian=True)
    return N, P, Kinv


def brute(setup, l, offset, D, d):
    N, P, Kinv = setup
    x = real_obs(N, l, offset).reshape(-1)
    y = real_obs(N, l, offset, D, d).reshape(-1)
    Cy = apply_cov(y.reshape(1, 4, N, N, N, N)).reshape(-1)
    Cx = apply_cov(x.reshape(1, 4, N, N, N, N)).reshape(-1)
    c = x @ Cy
    t = (P @ Cx) @ Kinv @ (P @ Cy)
    return c, c - t


def check():
    ok = True
    for (M, l, w) in [(4, 2, 0.5), (2, 4, 0.7)]:
        t0 = time.time()
        offsets = {'corner': 0, 'centre': l // 4}
        r = conditional(M, l, w, dirs=(0, 3), Dmax=1, offsets=offsets)
        setup = brute_setup(M, l, w)
        print(f"setup M={M} l={l}: {time.time() - t0:.1f}s", flush=True)
        for name, o in offsets.items():
            for d in (0, 3):
                for D in (0, 1):
                    cb, gb = brute(setup, l, o, D, d)
                    c, g = r[name][d]['C'][D], r[name][d]['Gamma'][D]
                    good = abs(cb - c) < 1e-8 * max(1, abs(cb)) and abs(gb - g) < 1e-7 * max(1e-3, abs(cb))
                    ok &= good
                    print(f"M={M} l={l} w={w} {name} dir={d} D={D}: brute C={cb:.10f} G={gb:.10f} | bloch C={c:.10f} "
                          f"G={g:.10f} {'OK' if good else 'MISMATCH'}", flush=True)
    print('CHECK', 'PASSED' if ok else 'FAILED', flush=True)


def run(M, ls, ws, out):
    allres = []
    for l in ls:
        for w in ws:
            t0 = time.time()
            r = conditional(M, l, w)
            dt = time.time() - t0
            for name in r:
                for d in r[name]:
                    e = r[name][d]
                    print(f"M={M} l={l:2d} w={w:.2f} {name:6s} dir={d} kappa={e['kappa']:.4f} "
                          f"R(D)=" + " ".join(f"{v:+.4f}" for v in e['R']) +
                          "  Gamma=" + " ".join(f"{v:.3e}" for v in e['Gamma']) +
                          "  C=" + " ".join(f"{v:.3e}" for v in e['C']) + f"  [{dt:.1f}s]", flush=True)
                    allres.append({'M': M, 'l': l, 'w': w, 'placement': name, 'dir': d, **e})
    if out:
        with open(out, 'w') as f:
            json.dump(allres, f, indent=1)


def diag(M, l, w, d=3, o=0):
    """q-resolved diagnostic of Gamma(D) along direction d (exploratory, after the pre-registered runs)."""
    qs, K, K0, H, H0, Cq = bloch(M, l, w, [o])
    ev, U = np.linalg.eigh(K)
    keep = ev > 1e-10 * ev.max(axis=-1, keepdims=True)
    Uh = np.einsum('qmi,qm->qi', U.conj(), H[o])
    contrib = np.abs(Uh) ** 2 * np.where(keep, 1.0 / np.where(keep, ev, 1.0), 0.0)   # (q, modes)
    tq = contrib.sum(-1)
    gq = Cq[o] - tq                       # conditional spectral weight per coarse momentum (q != 0)
    gq[0] = np.nan
    for D in range(M // 2 + 1):
        ph = np.real(np.exp(-1j * qs[:, d] * D))
        print(f"D={D}: Gamma part from q_d=pi: {np.nansum(np.where(np.isclose(qs[:, d], np.pi), gq * ph, 0)) / M**4:+.3e}, "
              f"rest {np.nansum(np.where(np.isclose(qs[:, d], np.pi), 0, gq * ph)) / M**4:+.3e}")
    # conditional weight as a function of q_d (summed over the other components)
    for v in np.unique(np.round(qs[:, d], 6)):
        sel = np.isclose(qs[:, d], v)
        print(f"q_d={v:.3f}: sum conditional weight {np.nansum(gq[sel]) / M**4:.3e}, unconditional {Cq[o][sel].sum() / M**4:.3e}, "
              f"min kept eig {np.min(np.where(keep[sel], ev[sel], np.inf)):.2e}")
    i = np.nanargmax(np.abs(gq))
    print('largest conditional weight at q =', qs[i] * M / TWO_PI, gq[i], 'eigs', ev[i])


if __name__ == '__main__':
    if sys.argv[1] == 'check':
        check()
    elif sys.argv[1] == 'diag':
        diag(int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]))
    else:
        M = int(sys.argv[2]); ls = [int(v) for v in sys.argv[3].split(',')]; ws = [float(v) for v in sys.argv[4].split(',')]
        out = sys.argv[sys.argv.index('--out') + 1] if '--out' in sys.argv else None
        run(M, ls, ws, out)
