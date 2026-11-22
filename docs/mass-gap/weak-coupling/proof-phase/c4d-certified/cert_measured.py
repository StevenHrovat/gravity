"""CERTIFIED upper bound on the W1 Dobrushin column of the measured anisotropic blocked action (PREREG.md in this folder).

Everything is one-dimensional: Bessel closed forms of the pure-fundamental reference law rho_A ~ exp(<A,u>) on S^3, |A| = r, enclosed by
interval arithmetic (mpmath iv, 100 bit) over cells of r, plus an explicit perturbation bound for the centre-blind / cubic couplings.
Usage:  python cert_measured.py            -> all fits at the box and at the margin scales, writes cert_measured.json
        python cert_measured.py --quick    -> base fit, coarse cells (float-ish exploration)
"""
import json, os, sys, time
os.environ["CUDA_VISIBLE_DEVICES"] = "-1"
from mpmath import iv, mp
iv.prec = 100

HERE = os.path.dirname(os.path.abspath(__file__))
KTAIL = 40

def Iv(x): return iv.mpf(x)
def U(m):
    """float >= the mpf m (rounded up)"""
    import math
    m = m.b if hasattr(m, "b") else m
    f = float(m)
    return f if f >= m else math.nextafter(f, math.inf)

def L(m):
    """float <= the mpf m (rounded down)"""
    import math
    m = m.a if hasattr(m, "a") else m
    f = float(m)
    return f if f <= m else math.nextafter(f, -math.inf)

def S(nu, y):
    """sum_k y^k / (k! (k+nu)!) for an interval y >= 0: terms nonnegative; truncated at KTAIL, tail <= t_K rho/(1 - rho),
    rho = y_hi/((K+1)(K+1+nu)) (ratio of consecutive terms is decreasing in k)."""
    f1 = Iv(1); f2 = Iv(1)
    for i in range(1, nu + 1): f2 = f2 * i
    num = Iv(1)
    t = num / (f1 * f2)
    acc = t
    for k in range(1, KTAIL + 1):
        f1 = f1 * k; f2 = f2 * (k + nu); num = num * y
        t = num / (f1 * f2)
        acc = acc + t
    rho = Iv(U(y.b)) / ((KTAIL + 1) * (KTAIL + 1 + nu))
    assert rho.b < 0.5
    tail = t * rho / (1 - rho)
    return acc + iv.mpf([0, U(tail.b)])

def cell_values(r):
    """for an interval r (nonnegative): the interval enclosures of x, q, x2, q2, zeta"""
    y1 = r * r / 4
    y2 = r * r
    S1a, S2a = S(1, y1), S(2, y1)
    S1b, S2b = S(1, y2), S(2, y2)
    T1 = S2a / S1a; T2 = S2b / S1b
    x = r / 2 * T1; q = 1 - Iv('1.5') * T1
    x2 = r * T2; q2 = 1 - Iv('1.5') * T2
    zeta = S1b / (S1a * S1a)
    return x, q, x2, q2, zeta

def cell_bound(r, eps):
    """upper bounds over the cell r: N_F = max_c2 main + max_c2 delta (the bound is concave in c^2, so endpoint-wise maxima are summed), zeta"""
    x, q, x2, q2, zeta = cell_values(r)
    mains, deltas = [], []
    sz = iv.sqrt(zeta)
    for c2 in (0, 1):
        if c2 == 1:
            V = q2 - 2 * x * x2 + x * x
            G1 = 4 * (q - x * x) ** 2
            Ef = iv.sqrt(q)
        else:
            V = (1 - q2) / 3
            G1 = 4 * ((1 - q) / 3) ** 2
            Ef = iv.sqrt((1 - q) / 3)
        A0 = zeta * V
        mains.append(iv.sqrt(A0 / 8 + Iv(5) / 24 * G1).b)
        deltas.append(eps * (iv.sqrt(A0) + Ef * (1 + eps) * sz) / iv.sqrt(Iv(3)))
    return U(max(mains) + max(d.b for d in deltas)), U(zeta.b), None

def sup_over_r(a, eps, ncell_per_unit=400):
    n = int(a * ncell_per_unit) + 1
    h = Iv(1) / ncell_per_unit
    best, zbest, argbest = 0.0, 0.0, None
    for i in range(n):
        r = iv.mpf([L((Iv(i) * h).a), U((Iv(i + 1) * h).b)])
        nf, zt, _ = cell_bound(r, eps)
        if nf > best: best, argbest = nf, (i / ncell_per_unit)
        zbest = max(zbest, zt)
    return best, zbest, argbest

SQ3 = iv.sqrt(Iv(3))
G3 = Iv(10) / 3 * iv.sqrt(Iv(5) / 18)      # sup |(6t^2-1) s| over t^2 + s^2 <= 1

def column(c, ncell=400):
    """c: dict of coupling bounds bFts bFss bAts bAss bTts bTss bR (nonneg). Returns dict with the certified column bound."""
    c = {k: Iv(repr(v)) for k, v in c.items()}      # decimal -> enclosing interval
    a_t = 6 * c["bFts"] + 18 * c["bR"]
    a_s = 2 * c["bFts"] + 4 * c["bFss"] + 18 * c["bR"]
    a = U(max(a_t.b, a_s.b))
    Dq_t = 6 * (4 * c["bAts"] / 3 + 2 * c["bTts"])
    Dq_s = 2 * (4 * c["bAts"] / 3 + 2 * c["bTts"]) + 4 * (4 * c["bAss"] / 3 + 2 * c["bTss"])
    Dq = U(max(Dq_t.b, Dq_s.b))
    eps = iv.exp(Iv(Dq)) - 1
    NF, zeta, rarg = sup_over_r(a, eps, ncell)
    NF = Iv(NF)                      # NF is an upper endpoint float; cell bounds are rigorous upper endpoints
    sz = iv.sqrt(Iv(zeta))
    zeff = (1 + eps) ** 2 * Iv(zeta)                      # >= E_Haar rho'^2 for every conditional law
    dev = iv.sqrt(zeff - 1)                               # >= || rho' - 1 ||_2
    ch = iv.sqrt(Iv(1) / 24) * iv.sqrt(zeff)              # >= |E_rho' h|
    cg = iv.sqrt(Iv('0.3125')) * iv.sqrt(zeff)            # >= |E_rho' g3|
    Nh = iv.sqrt(Iv(1) / 192) + (Iv(1) / 2 + ch) * dev / SQ3
    Ng = iv.sqrt(Iv('0.3125') / 15) + (G3 + cg) * dev / SQ3
    k_ts = c["bFts"] * NF + Iv(8) / 3 * c["bAts"] * Nh + c["bTts"] * Ng
    k_ss = c["bFss"] * NF + Iv(8) / 3 * c["bAss"] * Nh + c["bTss"] * Ng
    k_R = c["bR"] * NF
    col_t = 18 * k_ts + 90 * k_R
    col_s = 3 * (2 * k_ts + 4 * k_ss) + 90 * k_R
    col = U(max(col_t.b, col_s.b))
    # decomposition of the spatial column for the report
    fund = 3 * (2 * c["bFts"] + 4 * c["bFss"]) * NF + 90 * c["bR"] * NF
    adj = 3 * (2 * Iv(8) / 3 * c["bAts"] + 4 * Iv(8) / 3 * c["bAss"]) * Nh
    cub = 3 * (2 * c["bTts"] + 4 * c["bTss"]) * Ng
    return dict(a=a, Dq=Dq, eps=U(eps.b), N_F=U(NF.b), r_at_sup=rarg, zeta_sup=zeta, N_h=U(Nh.b), N_g=U(Ng.b),
                k_ts=U(k_ts.b), k_ss=U(k_ss.b), k_R=U(k_R.b), column_t=U(col_t.b), column_s=U(col_s.b),
                column=col, part_fund_s=U(fund.b), part_adj_s=U(adj.b), part_cubic_s=U(cub.b))

BOX = dict(bFts=0.0545, bFss=0.1725, bAts=0.0011, bAss=0.0020, bTts=0.0009, bTss=0.0009, bR=0.0086)
CENTRAL = dict(bFts=0.05396, bFss=0.17113, bAts=0.00060, bAss=0.00149, bTts=0.00009, bTss=0.00033, bR=0.0084)
FITS = {"base": ("bT", "bR"), "ext_T": ("bR",), "ext_R": ("bT",), "ext_TR": ()}

def zero(c, keys):
    c = dict(c)
    for k in keys:
        if k == "bT": c["bTts"] = c["bTss"] = 0.0
        else: c[k] = 0.0
    return c

def main():
    quick = "--quick" in sys.argv
    ncell = 100 if quick else 400
    res = {}
    t0 = time.time()
    scales = [1.0] if quick else [1.0, 1.1, 1.25, 1.5, 2.0]
    fits = ["base"] if quick else list(FITS)
    for name in fits:
        res[name] = {}
        for s in scales:
            c = zero({k: v * s for k, v in BOX.items()}, FITS[name])
            r = column(c, ncell)
            res[name][f"box_x{s}"] = r
            print(f"{name:7s} box x{s:<4}: column <= {r['column']:.5f} (spatial {r['column_s']:.5f}, temporal {r['column_t']:.5f}); "
                  f"fund {r['part_fund_s']:.4f} adj {r['part_adj_s']:.4f} cubic {r['part_cubic_s']:.4f}; N_F* {r['N_F']:.5f} at r~{r['r_at_sup']}, "
                  f"zeta* {r['zeta_sup']:.4f}, a {r['a']:.4f}, Dq {r['Dq']:.4f}  [{time.time()-t0:.0f}s]", flush=True)
        c = zero(CENTRAL, FITS[name])
        r = column(c, ncell)
        res[name]["central"] = r
        print(f"{name:7s} central fit : column <= {r['column']:.5f} (spatial {r['column_s']:.5f}, temporal {r['column_t']:.5f}); N_F* {r['N_F']:.5f}  [{time.time()-t0:.0f}s]", flush=True)
    if not quick:
        json.dump(dict(box=BOX, central=CENTRAL, results=res), open(os.path.join(HERE, "cert_measured.json"), "w"), indent=1)

if __name__ == "__main__":
    main()
