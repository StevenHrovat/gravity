# Multi-site, correlated-shell test of the twisted blocking on a periodic lattice (TWIST.md section 4).
# Questions fixed before running:
#  V1 gauge covariance: plaquette angles of the blocked field are the same with and without a random gauge transformation
#     of the input (for Balaban's (0.4) and for the twisted rule).
#  V2 small fields: with no deep cores the twisted rule creates no label and its output equals (0.4) exactly.
#  T1 no trapping: start from a correlated background (a random gauge transformation of a field built from the lowest
#     Fourier modes, bond phases eps/N, so that it stays small at every level; plus, optionally, white noise of
#     amplitude delta per bond, which is scale-stable under blocking only in d = 4) plus deep cores at random sites
#     (exact vortex stars at block centres and off-centre, and generic deep cores: Haar values on 1-3 bonds).
#  (A first version used a background smoothed over 5 sites with amplitude eps; in d = 2 it roughened under blocking
#   for both rules, which tests the background, not the cores; kept out of the record, see TWIST.md 4.)
#     After each blocking level count (a) deep plaquettes of the blocked field (angle > 0.5) and (b) for the twisted rule,
#     deep plaquettes of the label-corrected field ("unexplained") and label vortex plaquettes (carried cores).
#     No trapping = unexplained deep plaquettes vanish after a few levels while carried cores may remain.
# Blocking: Balaban [I] (0.4) with the exact contour families G(y,x) (all orders of the nonzero directions), weights
#   L^-d |G|^-1 |G'|^-1, principal log with log(-1) := 0. Twisted rule (TWIST.md 1): S = lam*U, U' = lam' * M(S),
#   lam'(c) = product of lam along the straight path of c; labels created at block centres where a non-trivial
#   star sign pattern sigma makes all plaquettes at the centre smooth (corrected angle < theta_c) and some are deep.
# Usage: python -I lattice_twist.py d L levels eps [seed] [delta] [cores_per_kind] [kinds, e.g. vc,vo,g]     (CPU only; d=2 L=5 levels=3, d=3 L=3 levels=3,
#        d=4 L=3 levels=2 each take seconds to a few minutes)
import sys, itertools, time
import numpy as np

d = int(sys.argv[1]); L = int(sys.argv[2]); LEV = int(sys.argv[3]); EPS = float(sys.argv[4])
SEED = int(sys.argv[5]) if len(sys.argv) > 5 else 1
DELTA = float(sys.argv[6]) if len(sys.argv) > 6 else 0.0
NCORE = int(sys.argv[7]) if len(sys.argv) > 7 else 0
KINDS = sys.argv[8].split(',') if len(sys.argv) > 8 else ['vc', 'vo', 'g']
TH_DEEP = 0.5; TH_C = 0.6
h = (L - 1) // 2


# ---------- quaternions (SU(2)) ----------
def qmul(a, b):
    w1, x1, y1, z1 = np.moveaxis(a, -1, 0); w2, x2, y2, z2 = np.moveaxis(b, -1, 0)
    return np.stack([w1*w2 - x1*x2 - y1*y2 - z1*z2, w1*x2 + x1*w2 + y1*z2 - z1*y2,
                     w1*y2 - x1*z2 + y1*w2 + z1*x2, w1*z2 + x1*y2 - y1*x2 + z1*w2], -1)


def qinv(a):
    return a * np.array([1.0, -1.0, -1.0, -1.0])


def qlog(a):
    w = np.clip(a[..., 0], -1.0, 1.0); v = a[..., 1:]
    th = np.arccos(w); s = np.linalg.norm(v, axis=-1)
    fac = np.where(s > 1e-14, th / np.maximum(s, 1e-300), 1.0)
    out = v * fac[..., None]
    return np.where((w <= -1.0 + 1e-15)[..., None], 0.0, out)


def qexp(v):
    th = np.linalg.norm(v, axis=-1); s = np.where(th > 1e-14, np.sin(th) / np.maximum(th, 1e-300), 1.0)
    return np.concatenate([np.cos(th)[..., None], v * s[..., None]], -1)


def angle(a):
    return np.arccos(np.clip(a[..., 0], -1.0, 1.0))


# ---------- lattice helpers: U[mu] has shape (N,)*d + (4,), bond (x, x+e_mu) ----------
def shift_idx(N, coords):
    return tuple(np.mod(c, N) for c in coords)


def transport(U, starts, steps):
    """Parallel transport from each start (tuple of index arrays) along steps [(mu, +-1), ...]."""
    N = U.shape[1]
    pos = [c.copy() for c in starts]
    T = None
    for mu, sg in steps:
        if sg > 0:
            g = U[mu][shift_idx(N, pos)]
            pos[mu] = pos[mu] + 1
        else:
            pos[mu] = pos[mu] - 1
            g = qinv(U[mu][shift_idx(N, pos)])
        T = g if T is None else qmul(T, g)
    if T is None:
        T = np.zeros(starts[0].shape + (4,)); T[..., 0] = 1.0
    return T


def plaquettes(U, mu, nu):
    N = U.shape[1]
    idx = np.indices((N,) * d)
    st = [idx[i] for i in range(d)]
    return transport(U, st, [(mu, 1), (nu, 1), (mu, -1), (nu, -1)])


def contour_steps(r):
    """All shortest paths G(0, r): one per order of the nonzero directions."""
    nz = [i for i in range(d) if r[i] != 0]
    out = []
    for perm in (itertools.permutations(nz) if nz else [()]):
        st = []
        for i in perm:
            st += [(i, 1 if r[i] > 0 else -1)] * abs(r[i])
        out.append(st)
    return out


def rev(steps):
    return [(mu, -sg) for mu, sg in reversed(steps)]


OFFS = list(itertools.product(range(-h, h + 1), repeat=d))
CONT = {r: contour_steps(r) for r in OFFS}


def block_04(U):
    """Balaban (0.4) block field on the coarse torus."""
    N = U.shape[1]; Nc = N // L
    I = np.indices((Nc,) * d)
    cen = [I[i] * L + h for i in range(d)]
    out = np.empty((d,) + (Nc,) * d + (4,))
    for mu in range(d):
        straight = [(mu, 1)] * L
        Uc = transport(U, cen, straight)
        Uci = qinv(Uc)
        acc = np.zeros((Nc,) * d + (3,))
        for r in OFFS:
            G = CONT[r]
            TG = [transport(U, cen, g) for g in G]
            xs = [cen[i] + r[i] + (L if i == mu else 0) for i in range(d)]      # x' = x + L e_mu
            Tseg = transport(U, [cen[i] + r[i] for i in range(d)], straight)
            cplus = [cen[i] + (L if i == mu else 0) for i in range(d)]
            TGp = [transport(U, xs, rev(g)) for g in G]                         # from x' back to c_+ (reverse of G(c_+, x'))
            w = 1.0 / (L ** d * len(G) * len(G))
            for a in TG:
                base = qmul(a, Tseg)
                for b in TGp:
                    acc += w * qlog(qmul(qmul(base, b), Uci))
        out[mu] = qmul(qexp(acc), Uc)
    return out


def decimate_labels(lam):
    """lam'(c) = product of lam along the straight path of c (Z2 straight-path decimation)."""
    N = lam.shape[1]; Nc = N // L
    I = np.indices((Nc,) * d)
    out = np.empty((d,) + (Nc,) * d)
    for mu in range(d):
        p = np.ones((Nc,) * d)
        pos = [I[i] * L + h for i in range(d)]
        for _ in range(L):
            p = p * lam[mu][shift_idx(N, pos)]
            pos[mu] = pos[mu] + 1
        out[mu] = p
    return out


def apply_lam(U, lam):
    return U * lam[..., None]


def create_labels(U, lam):
    """At each block centre: if the plaquettes at the centre (of the corrected field) are deep and a non-trivial star
    sign pattern makes all of them smooth, multiply the labels of the star by it. Returns new lam and count."""
    N = U.shape[1]; Nc = N // L
    S = apply_lam(U, lam)
    I = np.indices((Nc,) * d)
    cen = [I[i] * L + h for i in range(d)]
    star = [(mu, s) for mu in range(d) for s in (1, -1)]
    # plaquettes at the centre in the quadrant (b, b'), b, b' non-collinear
    P = {}
    for (m1, s1), (m2, s2) in itertools.combinations(star, 2):
        if m1 == m2:
            continue
        P[((m1, s1), (m2, s2))] = transport(S, cen, [(m1, s1), (m2, s2), (m1, -s1), (m2, -s2)])
    sign = {k: np.where(v[..., 0] < 0, -1.0, 1.0) for k, v in P.items()}
    deep = np.zeros((Nc,) * d, bool)
    for v in P.values():
        deep |= angle(v) > TH_DEEP
    # sigma relative to sigma(+e0) = +1: sigma_b = sign(+e0, b) for b not on axis 0; then axis 0 negative via (+e1)
    sig = {(0, 1): np.ones((Nc,) * d)}
    for b in star:
        if b[0] != 0:
            sig[b] = sign[((0, 1), b)]
    sig[(0, -1)] = sign[((0, -1), (1, 1))] * sig[(1, 1)]
    ok = np.ones((Nc,) * d, bool); nontriv = np.zeros((Nc,) * d, bool)
    for (b1, b2), v in P.items():
        corr = v * (sig[b1] * sig[b2])[..., None]
        ok &= angle(corr) < TH_C
    for b in star:
        nontriv |= sig[b] < 0
    make = deep & ok & nontriv
    lam_new = lam.copy()
    for (mu, s) in star:
        if s > 0:
            pos = cen
        else:
            pos = [cen[i] - (1 if i == mu else 0) for i in range(d)]
        idx = shift_idx(N, pos)
        cur = lam_new[mu][idx]
        lam_new[mu][idx] = np.where(make, cur * sig[(mu, s)], cur)
    # isolation (TWIST.md 1): after correction no deep plaquette may remain with a corner within distance 1 of the centre
    Snew = apply_lam(U, lam_new)
    deepmap = np.zeros((N,) * d, bool)
    for m1, m2 in itertools.combinations(range(d), 2):
        a = angle(plaquettes(Snew, m1, m2)) > TH_DEEP
        for sh in itertools.product((0, 1), repeat=2):     # mark all four corners of a deep plaquette
            b = a
            if sh[0]: b = np.roll(b, 1, axis=m1)
            if sh[1]: b = np.roll(b, 1, axis=m2)
            deepmap |= b
    near = deepmap.copy()
    for ax in range(d):
        near = near | np.roll(near, 1, axis=ax) | np.roll(near, -1, axis=ax)
    isolated = ~near[shift_idx(N, cen)]
    make = make & isolated
    lam = lam.copy()
    for (mu, s) in star:
        if s > 0:
            pos = cen
        else:
            pos = [cen[i] - (1 if i == mu else 0) for i in range(d)]
        idx = shift_idx(N, pos)
        cur = lam[mu][idx]
        lam[mu][idx] = np.where(make, cur * sig[(mu, s)], cur)
    return lam, int(make.sum())


def drop_labels(U, lam):
    """Drop the labels of the star of every site at which a label vortex plaquette meets a smooth plaquette of U
    (the label no longer describes the field). Returns new lam and number of sites dropped."""
    N = U.shape[1]
    bad = np.zeros((N,) * d, bool)
    one = np.array([1.0, 0, 0, 0])
    for m1, m2 in itertools.combinations(range(d), 2):
        lp = plaquettes(lam[..., None] * one, m1, m2)[..., 0] < 0
        sm = angle(plaquettes(U, m1, m2)) < TH_DEEP
        b = lp & sm
        for sh in itertools.product((0, 1), repeat=2):
            c = b
            if sh[0]: c = np.roll(c, 1, axis=m1)
            if sh[1]: c = np.roll(c, 1, axis=m2)
            bad |= c
    lam = lam.copy()
    for mu in range(d):
        kill = bad | np.roll(bad, -1, axis=mu)                # bond (x, x+e_mu) touches a bad site
        lam[mu] = np.where(kill, 1.0, lam[mu])
    return lam, int(bad.sum())


def stats(U, lam=None):
    deep = vort = unexpl = 0; total = 0
    for mu, nu in itertools.combinations(range(d), 2):
        p = plaquettes(U, mu, nu)
        deep += int((angle(p) > TH_DEEP).sum()); total += p[..., 0].size
        if lam is not None:
            S = apply_lam(U, lam)
            ps = plaquettes(S, mu, nu)
            unexpl += int((angle(ps) > TH_DEEP).sum())
            lp = plaquettes(lam[..., None] * np.array([1.0, 0, 0, 0]), mu, nu)[..., 0]
            vort += int((lp < 0).sum())
    return deep, unexpl, vort, total


# ---------- initial field ----------
def smooth_field(N, rng):
    """Lowest Fourier modes (|k|_inf <= 1), bond phases of size eps/N, plus white noise delta."""
    U = np.empty((d,) + (N,) * d + (4,))
    X = np.indices((N,) * d).astype(float)
    for mu in range(d):
        a = np.zeros((N,) * d + (3,))
        for k in itertools.product((-1, 0, 1), repeat=d):
            if not any(k):
                continue
            ph = sum(2 * np.pi * k[i] * X[i] / N for i in range(d))
            c = rng.normal(size=3); s0 = rng.uniform(0, 2 * np.pi)
            a += np.cos(ph + s0)[..., None] * c
        a *= EPS / N
        if DELTA > 0:
            a += DELTA * rng.normal(size=a.shape)
        U[mu] = qexp(a)
    return U


def gauge(U, rng):
    N = U.shape[1]
    u = rng.normal(size=(N,) * d + (4,)); u /= np.linalg.norm(u, axis=-1, keepdims=True)
    V = np.empty_like(U)
    for mu in range(d):
        V[mu] = qmul(qmul(u, U[mu]), qinv(np.roll(u, -1, axis=mu)))
    return V


def add_cores(U, rng, n_vortex_c, n_vortex_off, n_generic):
    N = U.shape[1]
    U = U.copy()
    log = []
    for kind, n in (("vc", n_vortex_c), ("vo", n_vortex_off), ("g", n_generic)):
        for _ in range(n):
            if kind == "vc":
                y = [rng.integers(N // L) * L + h for _ in range(d)]
            else:
                y = [rng.integers(N) for _ in range(d)]
            if kind in ("vc", "vo"):
                axes = rng.permutation(d)[: max(1, d // 2)]          # flip the star bonds along these axes
                for mu in axes:
                    U[mu][tuple(y)] *= -1
                    ym = list(y); ym[mu] = (ym[mu] - 1) % N
                    U[mu][tuple(ym)] *= -1
            else:
                for _ in range(rng.integers(1, 4)):
                    mu = rng.integers(d)
                    g = rng.normal(size=4); g /= np.linalg.norm(g)
                    U[mu][tuple(y)] = g
            log.append(kind)
    return U


def run(U0, twisted, levels, label):
    U = U0; lam = np.ones(U.shape[:-1]); line = []
    for k in range(levels + 1):
        if twisted:
            de, un, vo, tot = stats(U, lam)
            line.append(f"L{k}: deep {de}/{tot} unexplained {un} label-vortex {vo}")
        else:
            de, _, _, tot = stats(U)
            line.append(f"L{k}: deep {de}/{tot}")
        if k == levels:
            break
        if twisted:
            lam, dropped = drop_labels(U, lam)
            lam, made = create_labels(U, lam)
            line[-1] += f" (+{made} labels, -{dropped} sites)"
            S = apply_lam(U, lam)
            U = apply_lam(block_04(S), decimate_labels(lam))
            lam = decimate_labels(lam)
        else:
            U = block_04(U)
    print(f"  {label}: " + " | ".join(line))
    return U, lam


if __name__ == "__main__":
    N = L ** LEV
    rng = np.random.default_rng(SEED)
    print(f"d={d} L={L} levels={LEV} N={N} eps={EPS} delta={DELTA} seed={SEED} paths/coarse-bond-direction="
          f"{sum(len(CONT[r]) ** 2 for r in OFFS)}")
    t0 = time.time()
    # V1 + V2: small field only, with and without gauge
    S0 = smooth_field(N, rng)
    g_rng = np.random.default_rng(SEED + 100)
    B1 = block_04(S0); B2 = block_04(gauge(S0, g_rng))
    dmax = max(np.abs(angle(plaquettes(B1, m, n)) - angle(plaquettes(B2, m, n))).max()
               for m, n in itertools.combinations(range(d), 2))
    lam0, made0 = create_labels(S0, np.ones(S0.shape[:-1]))
    Bt = apply_lam(block_04(apply_lam(S0, lam0)), decimate_labels(lam0))
    print(f"V1 gauge covariance (0.4): max |plaquette angle difference| = {dmax:.2e}")
    print(f"V2 small field: labels created {made0}; max |twisted - (0.4)| = {np.abs(Bt - B1).max():.2e}"
          f"   [{time.time() - t0:.0f}s]")
    # T1
    nb = (N // L) ** d
    nc = NCORE if NCORE > 0 else max(2, nb // 50)
    print(f"cores per kind: {nc} (vortex at centre, vortex off-centre, generic) on {nb} level-1 blocks")
    U0 = add_cores(S0, rng, nc if 'vc' in KINDS else 0, nc if 'vo' in KINDS else 0, nc if 'g' in KINDS else 0)
    print(f"kinds: {KINDS}")
    for gauged in (True,):
        Ug = gauge(U0, np.random.default_rng(SEED + 7)) if gauged else U0
        print(f"T1 ({'random gauge' if gauged else 'no gauge'}):")
        run(Ug, False, LEV, "(0.4)   ")
        run(Ug, True, LEV, "twisted ")
    print(f"done [{time.time() - t0:.0f}s]")
