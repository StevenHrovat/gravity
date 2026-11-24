# ROUTE-B.md check (i)/(iii): which nested-centre cores persist under the split blocking (SO(3) part averaged with
# Balaban's (0.4) using SO(3) logarithms, Z2 layer tau_p = sign tr U_p blocked by mod-2 Stokes over the flat tile).
# Configurations at a block centre y, star bonds in directions +-3, +-4 set to g, all other bonds 1 (Vortex.lean shape):
#   'centre'  g = -1                       (central: SO(3) part flat, Z2 layer carries it)
#   'equator' g = exp(i (pi/2 - delta/2) n.sigma)  (SO(3) rotation by pi - delta: near the SO(3) cut)
# Printed: coarse plaquettes at y in the mixed planes: SO(3) rotation angle of the averaged SO(3) field, and the
# mod-2 Stokes Z2 flux. Usage: python -I route_b_cores.py [delta]      (d = 4, L = 3, one level; seconds)
import sys, itertools
import numpy as np
sys.argv = [sys.argv[0], '4', '3', '1', '0.0'] + sys.argv[1:2]
DELTA = float(sys.argv[5]) if len(sys.argv) > 5 else 0.0
d, L = 4, 3
h = (L - 1) // 2
src = open(__file__.replace('route_b_cores.py', 'lattice_twist.py')).read()
ns = {'np': np, 'itertools': itertools, 'd': d, 'L': L, 'h': h}
body = src.split('# ---------- quaternions (SU(2)) ----------')[1].split('def decimate_labels')[0]
exec(body, ns)
qmul, qinv, qexp, transport, plaquettes, CONT, OFFS, rev = (ns[k] for k in
    ['qmul', 'qinv', 'qexp', 'transport', 'plaquettes', 'CONT', 'OFFS', 'rev'])


def so3_lift(a):
    """canonical SU(2) lift of the SO(3) class: w >= 0 (tie w = 0 kept as is)"""
    return np.where((a[..., 0] < 0)[..., None], -a, a)


def so3_log(a):
    a = so3_lift(a)
    w = np.clip(a[..., 0], -1.0, 1.0); v = a[..., 1:]
    th = np.arccos(w); s = np.linalg.norm(v, axis=-1)
    fac = np.where(s > 1e-14, th / np.maximum(s, 1e-300), 1.0)
    return v * fac[..., None]


def block_so3(U):
    N = U.shape[1]; Nc = N // L
    I = np.indices((Nc,) * d)
    cen = [I[i] * L + h for i in range(d)]
    out = np.empty((d,) + (Nc,) * d + (4,))
    for mu in range(d):
        straight = [(mu, 1)] * L
        Uc = transport(U, cen, straight); Uci = qinv(Uc)
        acc = np.zeros((Nc,) * d + (3,))
        for r in OFFS:
            G = CONT[r]
            TG = [transport(U, cen, g) for g in G]
            xs = [cen[i] + r[i] + (L if i == mu else 0) for i in range(d)]
            Tseg = transport(U, [cen[i] + r[i] for i in range(d)], straight)
            TGp = [transport(U, xs, rev(g)) for g in G]
            w = 1.0 / (L ** d * len(G) * len(G))
            for a in TG:
                base = qmul(a, Tseg)
                for b in TGp:
                    acc += w * so3_log(qmul(qmul(base, b), Uci))
        out[mu] = qmul(qexp(acc), Uc)
    return out


def tau(U, mu, nu):
    return np.where(plaquettes(U, mu, nu)[..., 0] < 0, -1, 1)


def stokes_tau(U, mu, nu):
    t = tau(U, mu, nu); N = U.shape[1]; Nc = N // L
    out = np.ones((Nc,) * d, dtype=int)
    for idx in itertools.product(range(Nc), repeat=d):
        base = [i * L + h for i in idx]
        prod = 1
        for a in range(L):
            for b in range(L):
                p = list(base); p[mu] += a; p[nu] += b
                prod *= t[tuple(np.mod(p, N))]
        out[idx] = prod
    return out


N = 9
for kind in ['centre', 'equator']:
    U = np.zeros((d,) + (N,) * d + (4,)); U[..., 0] = 1.0
    y = (h + L,) * d                                         # a block centre (coarse site 1,1,1,1)
    if kind == 'centre':
        g = np.array([-1.0, 0, 0, 0])
    else:
        g = np.array([np.sin(DELTA / 2), np.cos(DELTA / 2), 0, 0])
    for nu in (2, 3):                                        # directions 3, 4 (0-based 2, 3)
        U[nu][y] = g                                         # bond y -> y + e_nu
        ym = list(y); ym[nu] -= 1
        U[nu][tuple(ym)] = qinv(g)                           # bond y - e_nu -> y carries g^-1, i.e. y -> y - e_nu carries g
    V = block_so3(U)
    yc = (1,) * d
    print(f'--- {kind} (delta = {DELTA}) ---')
    for mu in (0, 1):
        for nu in (2, 3):
            for sm in (0, 1):
                for sn in (0, 1):
                    ycc = list(yc); ycc[mu] -= sm; ycc[nu] -= sn
                    P = plaquettes(V, mu, nu)[tuple(np.mod(ycc, N // L))]
                    rot = 2 * np.arccos(min(1.0, abs(P[0])))
                    st = stokes_tau(U, mu, nu)[tuple(np.mod(ycc, N // L))]
                    fine = plaquettes(U, mu, nu)
                    print(f'plane ({mu+1},{nu+1}) quadrant ({sm},{sn}): SO(3) rotation {rot:.4f}  mod-2 Stokes tau {st:+d}')
    allrot = max(2 * np.arccos(min(1.0, abs(plaquettes(V, a, b)[..., 0]).min())) for a in range(d) for b in range(a + 1, d))
    print(f'max coarse SO(3) plaquette rotation anywhere: {allrot:.4f}')
