"""c9b round 2, CPU check N2 (pre-registered in PREREG-N2.md): sharp sup-form columns of the fitted actions, TV-Lipschitz
constants, the W1-plus-smoothing Hamming count at L sqrt(sigma) = 2.80, and the direct Hamming route at larger L1.
All numbers are numerical (quadrature on S^3), about the fitted truncated plaquette action only.  numpy only, CPU."""
import itertools
import math
import time

import numpy as np

T0 = time.time()
rng = np.random.default_rng(20261123)

# base fits [F_ts, F_ss, A_ts, A_ss] from ../c3b-refit/runs-gpu/analysis.log (central values), with content verdicts
FITS = [
    # (beta, b, L sqrt(sigma), content, F_ts, F_ss, A_ts, A_ss)
    (2.3, 4, 1.40, "NO_CONTENT", 0.399, 0.832, -0.00798, 0.00794),
    (2.3, 8, 2.80, "PASS", 0.054, 0.171, -0.000595, 0.00149),
    (2.3, 16, 5.60, "NO_CONTENT", 0.0309, 0.0922, -0.000138, 0.000817),
    (2.4, 4, 1.03, "NO_CONTENT", 0.835, 1.33, -0.034, 0.00135),
    (2.4, 8, 2.06, "NO_CONTENT", 0.113, 0.338, -0.00161, 0.00343),
    (2.4, 16, 4.13, "NO_CONTENT", 0.0344, 0.104, -0.000154, 0.000692),
    (2.5, 4, 0.73, "NO_CONTENT", 1.3, 1.79, -0.0827, -0.0112),
    (2.5, 8, 1.46, "NO_CONTENT", 0.339, 0.704, -0.00728, 0.0052),
    (2.5, 16, 2.92, "NO_CONTENT", 0.0478, 0.149, -0.00048, 0.000958),
]
# c4d box at 2.80 (rounded up), for the reported 2.80 row as well
BOX280 = (0.0545, 0.1725, 0.0011, 0.0020)
C_W = 0.7318  # certified W1 column (c4d, base box, spatial; temporal 0.3045)


def grid(nc, nt, nf):
    """Midpoint grid on S^3 in Hopf-type angles; returns u (n,4) restricted to the first three coordinates and weights."""
    chi = (np.arange(nc) + 0.5) * math.pi / nc
    th = (np.arange(nt) + 0.5) * math.pi / nt
    ph = (np.arange(nf) + 0.5) * math.pi / nf  # u4 -> -u4 symmetry: phi in (0, pi) suffices
    C, Th, Ph = np.meshgrid(chi, th, ph, indexing="ij")
    u1 = np.cos(C)
    u2 = np.sin(C) * np.cos(Th)
    u3 = np.sin(C) * np.sin(Th) * np.cos(Ph)
    w = np.sin(C) ** 2 * np.sin(Th)
    w = (w / w.sum()).ravel()
    return np.stack([u1.ravel(), u2.ravel(), u3.ravel()], axis=1), w


G_COARSE = grid(48, 24, 24)
G_FINE = grid(160, 80, 80)


def tv_pair(g, beta, alpha, r, psi, t1, t2):
    u, w = g
    Ar = r * np.array([math.cos(t1), math.sin(t1) * math.cos(t2), math.sin(t1) * math.sin(t2)])
    s1 = np.array([1.0, 0.0, 0.0])
    s2 = np.array([math.cos(psi), math.sin(psi), 0.0])
    base = u @ Ar
    t_1 = u @ s1
    t_2 = u @ s2
    h1 = base + beta * t_1 + (alpha / 3) * (4 * t_1 ** 2 - 1)
    h2 = base + beta * t_2 + (alpha / 3) * (4 * t_2 ** 2 - 1)
    m = max(h1.max(), h2.max())
    p1 = w * np.exp(h1 - m)
    p2 = w * np.exp(h2 - m)
    return 0.5 * np.abs(p1 / p1.sum() - p2 / p2.sum()).sum()


def lip_pair(g, beta, alpha, r, t1, t2):
    """(1/2) E_rho |G - E G|, G = (beta + (8 alpha/3) t) <u, b>, s = e1, b = e2; A_r direction (t1, t2)."""
    u, w = g
    Ar = r * np.array([math.cos(t1), math.sin(t1) * math.cos(t2), math.sin(t1) * math.sin(t2)])
    t = u[:, 0]
    h = u @ Ar + beta * t + (alpha / 3) * (4 * t ** 2 - 1)
    p = w * np.exp(h - h.max())
    p /= p.sum()
    G = (beta + (8 * alpha / 3) * t) * u[:, 1]
    return 0.5 * (p * np.abs(G - (p * G).sum())).sum()


def maximise(f, bounds, n0, steps=80):
    """Coarse grid over the box `bounds` (list of (lo, hi, n)), then a shrinking random local search."""
    axes = [np.linspace(lo, hi, n) for lo, hi, n in bounds]
    best, bx = -1.0, None
    for x in itertools.product(*axes):
        v = f(*x)
        if v > best:
            best, bx = v, np.array(x)
    span = np.array([hi - lo for lo, hi, _ in bounds])
    lo = np.array([b[0] for b in bounds])
    hi = np.array([b[1] for b in bounds])
    scale = 0.25
    for _ in range(steps):
        x = np.clip(bx + rng.normal(size=len(bx)) * span * scale, lo, hi)
        v = f(*x)
        if v > best:
            best, bx = v, x
        else:
            scale *= 0.97
    return best, bx


def q_tilt(D):
    return (3 * math.exp(D) - 1) / 2


def pair_coeffs(beta, alpha, a_recv, D_rest):
    """Sharp sup-form TV coefficient and TV-Lipschitz constant for one incidence."""
    beta, alpha = abs(beta), alpha
    rmax = max(a_recv - beta, 0.0)
    f = lambda r, psi, t1, t2: tv_pair(G_COARSE, beta, alpha, r, psi, t1, t2)
    _, x = maximise(f, [(0, rmax, 4), (math.pi / 2, math.pi, 4), (0, math.pi, 5), (0, math.pi / 2, 3)], 0)
    tv = tv_pair(G_FINE, beta, alpha, *x)
    fl = lambda r, t1, t2: lip_pair(G_COARSE, beta, alpha, r, t1, t2)
    _, y = maximise(fl, [(0, rmax, 4), (0, math.pi, 7), (0, math.pi / 2, 4)], 0)
    lam = lip_pair(G_FINE, beta, alpha, *y)
    return q_tilt(D_rest) * tv, q_tilt(D_rest) * lam, x, y


def fit_coeffs(Fts, Fss, Ats, Ass):
    a_s = 4 * abs(Fss) + 2 * abs(Fts)
    a_t = 6 * abs(Fts)
    out = {}
    # receiving link spatial: other plaquettes' adjoint oscillation (4/3)|alpha| summed over its other 5 plaquettes (crudely all 6)
    D_s = (4 / 3) * (4 * abs(Ass) + 2 * abs(Ats))
    D_t = (4 / 3) * (6 * abs(Ats))
    for recv, a, D in (("s", a_s, D_s), ("t", a_t, D_t)):
        for pt, beta, alpha in (("ss", Fss, Ass), ("ts", Fts, Ats)):
            if recv == "t" and pt == "ss":
                continue
            out[(recv, pt)] = pair_coeffs(beta, alpha, a, D)
    crude = {pt: math.tanh(abs(b)) + math.tanh(2 * abs(al) / 3) for pt, b, al in (("ss", Fss, Ass), ("ts", Fts, Ats))}
    return out, crude


# ---------- lattice bookkeeping: links, plaquette neighbours, colour classes ----------
def lattice(n=4):
    sites = list(itertools.product(range(n), repeat=4))
    links = [(x, mu) for x in sites for mu in range(4)]
    idx = {l: i for i, l in enumerate(links)}

    def add(x, mu):
        y = list(x)
        y[mu] = (y[mu] + 1) % n
        return tuple(y)

    nb = {i: [] for i in range(len(links))}
    for x in sites:
        for mu in range(4):
            for nu in range(mu + 1, 4):
                pl = [(x, mu), (add(x, mu), nu), (add(x, nu), mu), (x, nu)]
                ii = [idx[l] for l in pl]
                typ = "ts" if 0 in (mu, nu) else "ss"
                for a in ii:
                    for b in ii:
                        if a != b:
                            nb[a].append((b, typ))
    return links, nb


LINKS, NB = lattice(4)


def colour(l):
    x, mu = l
    return 2 * mu + (sum(x[i] for i in range(4) if i != mu) % 2)


def check_colouring():
    for a, lst in NB.items():
        for b, _ in lst:
            assert colour(LINKS[a]) != colour(LINKS[b]), "colouring fails"
        assert len(lst) == 18
    return True


def ltype(l):
    return "t" if l[1] == 0 else "s"


def class_matrix(coef):
    """M[k][l] = sum over x in class k adjacent to a representative z of class l of coef(x, z)."""
    M = np.zeros((8, 8))
    for cl in range(8):
        z = next(i for i, l in enumerate(LINKS) if colour(l) == cl)
        for x, typ in NB[z]:
            M[colour(LINKS[x]), cl] += coef(ltype(LINKS[x]), typ)
    return M


def best_order(M):
    best = (math.inf, None)
    for perm in itertools.permutations(range(8)):
        pos = {c: i for i, c in enumerate(perm)}
        L = np.array([[M[k, l] if pos[l] < pos[k] else 0.0 for l in range(8)] for k in range(8)])
        K = np.eye(8)
        P = np.eye(8)
        for _ in range(7):
            P = L @ P
            K = K + P
        ks = K.sum(axis=0).max()
        if ks < best[0]:
            best = (ks, perm)
    return best


def n_adj(l):
    offs = [tuple(int(i == m) * s for i in range(4)) for m in range(4) for s in (1, -1)]
    offs += [tuple(int(i == m) - int(i == n) for i in range(4)) for m in range(4) for n in range(4) if m != n]
    box = set(itertools.product(range(l), repeat=4))
    out = set()
    for x in box:
        for o in offs:
            u = tuple(x[i] - o[i] for i in range(4))  # u + o = x in box
            if u not in box:
                out.add(u)
    return len(out)


def l_min(kappa):
    l = 1
    while (8 * l ** 3 + 12 * l ** 2) * kappa >= l ** 4:
        l += 1
        if l > 10 ** 7:
            return None
    return l


# ---------------------------------- run ----------------------------------
print("N2 (pre-registered, PREREG-N2.md); numerical; fitted actions only")
assert check_colouring()
print("colouring: 8 classes, no two links of a class share a plaquette, 18 neighbours per link: OK")
for l in (2, 3, 4, 5):
    assert n_adj(l) == 8 * l ** 3 + 12 * l ** 2, (l, n_adj(l))
print("N_adj(l) = 8 l^3 + 12 l^2 checked by enumeration for l = 2..5")

# controls
beta = 0.17
t = np.linspace(-1, 1, 400001)
dens = np.exp(beta * t) * np.sqrt(1 - t ** 2)
exact = (np.sign(t) * dens).sum() / dens.sum()
quad = tv_pair(G_FINE, beta, 0.0, 0.0, math.pi, 0.0, 0.0)
print(f"control (i): TV(vMF(+s), vMF(-s)) beta={beta}: quadrature {quad:.6f}, 1D integral {exact:.6f}, rel {abs(quad-exact)/exact:.2e}")
small = tv_pair(G_FINE, 1e-3, 0.0, 0.0, math.pi, 0.0, 0.0) / 1e-3
print(f"control (ii): small-beta sharp/beta {small:.5f} vs 4/(3 pi) = {4/(3*math.pi):.5f}")
ctrl_ok = abs(quad - exact) / exact < 1e-2 and abs(small - 4 / (3 * math.pi)) / (4 / (3 * math.pi)) < 1e-2

rows = []
for (b_, bb, L, content, Fts, Fss, Ats, Ass) in FITS:
    co, crude = fit_coeffs(Fts, Fss, Ats, Ass)
    C = {k: v[0] for k, v in co.items()}
    Lm = {k: v[1] for k, v in co.items()}
    # rows (receiving link): spatial 12 ss + 6 ts, temporal 18 ts
    row_s = 12 * C[("s", "ss")] + 6 * C[("s", "ts")]
    row_t = 18 * C[("t", "ts")]
    # columns via the class matrix (coefficients depend on receiving type and plaquette type)
    coefC = lambda rt, pt: C[(rt, pt)]
    coefL = lambda rt, pt: Lm[(rt, pt)]
    MC = class_matrix(coefC)
    ML = class_matrix(coefL)
    colC = MC.sum(axis=0)  # per class of z
    colL = ML.sum(axis=0)
    crude_s = 12 * crude["ss"] + 6 * crude["ts"]
    crude_t = 18 * crude["ts"]
    r = dict(beta=b_, b=bb, L=L, content=content, C=C, Lam=Lm, crude_s=crude_s, crude_t=crude_t, row_s=row_s, row_t=row_t,
             colC=colC, colL=colL, MC=MC, ML=ML, ratio={k: C[k] / crude[k[1]] for k in C})
    rows.append(r)
    print(f"\nbeta={b_} b={bb} L sqrt(sigma)={L:.2f} content={content}  F_ts={Fts} F_ss={Fss} A_ts={Ats} A_ss={Ass}")
    for k in sorted(C):
        print(f"   pair recv={k[0]} plaq={k[1]}: sharp C={C[k]:.5f}  crude={crude[k[1]]:.5f}  ratio={r['ratio'][k]:.3f}  "
              f"Lam={Lm[k]:.5f}/rad  argmax(r,psi,t1,t2)={np.round(co[k][2],3)}")
    print(f"   crude columns (N1 form): spatial {crude_s:.4f} temporal {crude_t:.4f}")
    print(f"   sharp rows: spatial {row_s:.4f} temporal {row_t:.4f};  sharp columns per class (z): "
          f"max {colC.max():.4f} (temporal-z {colC[0]:.4f}, spatial-z {colC[2]:.4f})")
    print(f"   TV-Lipschitz columns: max {colL.max():.4f}/rad (temporal-z {colL[0]:.4f}, spatial-z {colL[2]:.4f})")
    c_tv = max(colC.max(), row_s, row_t)
    if c_tv < 1:
        kap = colC.max() / (1 - colC.max())
        print(f"   DIRECT Hamming route: c_TV = {colC.max():.4f} < 1, kappa_Ham <= {kap:.3f}, l_min = {l_min(kap)}")
    else:
        print(f"   direct Hamming route unavailable (sharp column {colC.max():.4f} >= 1)")

# the 2.80 box corner as well
print("\n2.80 at the c4d box corner (|F_ts|,|F_ss|,|A_ts|,|A_ss|) =", BOX280)
co, crude = fit_coeffs(*BOX280)
Cb = {k: v[0] for k, v in co.items()}
Lb = {k: v[1] for k, v in co.items()}
MCb = class_matrix(lambda rt, pt: Cb[(rt, pt)])
MLb = class_matrix(lambda rt, pt: Lb[(rt, pt)])
print(f"   sharp column max {MCb.sum(axis=0).max():.4f}; rows spatial {12*Cb[('s','ss')]+6*Cb[('s','ts')]:.4f}; "
      f"Lipschitz column max {MLb.sum(axis=0).max():.4f}/rad")

# smoothing at 2.80 (central fit and box corner)
for name, MC, ML in (("central", rows[1]["MC"], rows[1]["ML"]), ("box corner", MCb, MLb)):
    ks, perm = best_order(MC)
    colTV = MC.sum(axis=0).max()
    colL = ML.sum(axis=0).max()
    D_tot = math.pi * C_W / (1 - C_W)
    kap = ks * (colTV + colL * D_tot)
    print(f"\nW1 + smoothing at 2.80 ({name}): best class order {perm}, K_s = {ks:.3f}; col_TV = {colTV:.4f}, "
          f"Lam_col = {colL:.4f}/rad, W1 total pi c_W/(1 - c_W) = {D_tot:.3f} rad")
    print(f"   kappa_Ham <= K_s (col_TV + Lam_col D) = {kap:.2f};  l_min (gamma_Z = 0) = {l_min(kap)};  "
          f"l_min (gamma_Z = 1/2) = {l_min(2*kap)}")

# verdicts
r280 = rows[1]
P1 = all(0.35 <= v <= 0.55 for r in rows for v in r["ratio"].values())
P2 = 0.85 <= max(r280["colC"].max(), r280["row_s"]) <= 1.20
big = [r for r in rows if r["L"] in (2.92, 4.13, 5.60)]
P3 = all(max(r["colC"].max(), r["row_s"], r["row_t"]) < 1 for r in big)
P4 = True
for b_ in (2.3, 2.4, 2.5):
    seq = [max(r["colC"].max(), r["row_s"]) for r in sorted([r for r in rows if r["beta"] == b_], key=lambda r: r["L"])]
    P4 &= all(seq[i + 1] < seq[i] for i in range(len(seq) - 1))
P5 = 0.4 <= r280["colL"].max() <= 0.9
ks, _ = best_order(r280["MC"])
kap280 = ks * (r280["colC"].max() + r280["colL"].max() * math.pi * C_W / (1 - C_W))
lm = l_min(kap280)
P6 = ks <= 1e4 and lm is not None and lm <= 1e5
P7 = ctrl_ok and abs(r280["crude_s"] - 2.397) < 0.02
print("\nmin/max ratio sharp/crude:", min(v for r in rows for v in r["ratio"].values()),
      max(v for r in rows for v in r["ratio"].values()))
for n, v in (("P1", P1), ("P2", P2), ("P3", P3), ("P4", P4), ("P5", P5), ("P6", P6), ("P7", P7)):
    print(n, "PASS" if v else "FAIL")
print(f"runtime {time.time()-T0:.0f} s")
