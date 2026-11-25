"""Certificate (PREREG step 2): sup over ALL class angles of |log rho_n - log K_t| for one 2D SU(2) Wilson block.

rho_n = w_beta^{*n} = sum_k k d_k(beta)^n chi_k,  K_t = sum_k k exp(-t (k^2-1)/4) chi_k,  k = 2j+1 = 1, 2, 3, ...
chi_k(th) = sum_{l = -(k-1), -(k-3), ..., k-1} cos(l th).
Tuning: beta_n is a fixed rational near the root of d_2(beta)^n = exp(-3t/4); then t_n := -(4n/3) log d_2(beta_n) is
enclosed, and K is evaluated at t_n (exact tuning by the block observable <chi_2>, with t_n within the printed interval).

Rigour: mpmath interval arithmetic (directed rounding, 50 digits). Bessel I_k(beta) for k <= KMAX by the power series
(positive terms) with a geometric tail bound; for k > KMAX, I_k/I_{k-1} < beta/(2k) (from I_{k-1} - I_{k+1} =
(2k/beta) I_k and I_{k+1} > 0), so d_k^n decays at least like 2^{-n} per step once k >= beta. Character sums truncated
at k <= KC with tail bounds T_r >= sum_{k>KC} k |c_k| sup|chi_k^{(r)}|, sup|chi_k^{(r)}| <= k (k-1)^r.
Sup over theta in [0, pi]: G equal cells; at the centre the derivatives of rho and K up to order R are enclosed; on the
cell rho, rho', rho'' are enclosed by Taylor polynomials with the remainder S_{R+1} = global bound of |rho^{(R+1)}|;
f = log rho - log K is enclosed on the cell by f(c) + f'(c) h + f''(cell) h^2/2. Output: certified upper bound of
delta = sup|f| and a certified lower bound (max over cell centres of |f(c)|)."""
import json, sys, time
from mpmath import iv, mp, mpf
iv.dps = 50; mp.dps = 50
R = 6
LO = lambda x: mp.make_mpf(x._mpi_[0])
HI = lambda x: mp.make_mpf(x._mpi_[1])

def fact_iv(n):
    r = iv.mpf(1)
    for i in range(2, n + 1): r = r * i
    return r

def besseli(nu, x):
    X = iv.mpf(x); h2 = (X / 2) ** 2
    term = (X / 2) ** nu / fact_iv(nu); s = term; m = 0
    while True:
        m += 1
        term = term * h2 / (m * (m + nu)); s = s + term
        q = h2 / ((m + 1) * (m + 1 + nu))
        if HI(q) < 0.5 and HI(term) < LO(s) * mpf('1e-45'):
            return s + iv.mpf([0, HI(term * q / (1 - q))])

def certify(n, t_nominal, beta, KC=36, G=1000):
    t0 = time.time()
    beta = mpf(beta)
    KMAX = max(KC + 2, int(float(beta)) + 2)
    I = [None] + [besseli(k, beta) for k in range(1, KMAX + 1)]
    d = [None] + [I[k] / I[1] for k in range(1, KMAX + 1)]
    cr = [None] + [d[k] ** n for k in range(1, KMAX + 1)]          # rho coefficients
    tn = -(iv.mpf(4) * n / 3) * iv.log(d[2])                        # tuned t, enclosed
    ck = lambda k: iv.exp(-tn * (k * k - 1) / 4)
    cK = [None] + [ck(k) for k in range(1, KMAX + 1)]
    # tails T_r for r = 0..R+1, rho and K, beyond KC
    def tails(c, kind):
        T = []
        for r in range(R + 2):
            s = iv.mpf(0)
            for k in range(KC + 1, KMAX + 1):
                s = s + k * k * iv.mpf(k - 1) ** r * c[k]
            # beyond KMAX: ratio of successive terms <= Q
            if kind == 'rho':
                q1 = (iv.mpf(beta) / (2 * KMAX)) ** n
            else:
                q1 = iv.exp(-tn * (2 * KMAX + 1) / 4)
            Q = (iv.mpf(KMAX + 1) / KMAX) ** (r + 2) * q1
            assert HI(Q) < 1
            first = (KMAX + 1) ** 2 * iv.mpf(KMAX) ** r * c[KMAX] * q1
            s = s + first / (1 - Q)
            T.append(iv.mpf([0, HI(s)]))
        return T
    Tr, TK = tails(cr, 'rho'), tails(cK, 'K')
    # global bound of |F^{(R+1)}|: sum_{k<=KC} k |c_k| P_{R+1}(k) + tail, P_r(k) = sum_l |l|^r exactly
    def P(k, r): return sum(abs(l) ** r for l in range(-(k - 1), k, 2))
    Sr = sum((k * P(k, R + 1) * cr[k] for k in range(1, KC + 1)), iv.mpf(0)) + Tr[R + 1]
    SK = sum((k * P(k, R + 1) * cK[k] for k in range(1, KC + 1)), iv.mpf(0)) + TK[R + 1]
    PI = iv.pi
    w = PI / G
    up = mpf(0); lo = mpf(0); argmax = None
    fact = [1, 1, 2, 6, 24, 120, 720, 5040, 40320]
    for i in range(G):
        th = (PI * (2 * i + 1)) / (2 * G)          # cell centre (thin interval)
        h = iv.mpf([-HI(w / 2), HI(w / 2)])
        # trig of l*th for l = 0..KC-1 by direct evaluation (thin intervals)
        cs = [iv.cos(l * th) for l in range(KC)]; sn = [iv.sin(l * th) for l in range(KC)]
        # derivatives of cos(l th): r=0 cos, 1 -l sin, 2 -l^2 cos, 3 l^3 sin, 4 l^4 cos, ...
        def dcos(l, r):
            m = r % 4; lr = iv.mpf(l) ** r
            return [cs[l], -sn[l], -cs[l], sn[l]][m] * lr
        chi_prev2 = None
        Fr = [iv.mpf(0)] * (R + 1); FK = [iv.mpf(0)] * (R + 1)
        # chi_1 = 1, chi_2 = 2 cos th, chi_k = chi_{k-2} + 2 cos((k-1) th)
        chis = {1: [iv.mpf(1)] + [iv.mpf(0)] * R, 2: [2 * dcos(1, r) for r in range(R + 1)]}
        for k in range(3, KC + 1):
            chis[k] = [chis[k - 2][r] + 2 * dcos(k - 1, r) for r in range(R + 1)]
        for k in range(1, KC + 1):
            for r in range(R + 1):
                Fr[r] = Fr[r] + k * cr[k] * chis[k][r]
                FK[r] = FK[r] + k * cK[k] * chis[k][r]
        Fr = [Fr[r] + iv.mpf([-HI(Tr[r]), HI(Tr[r])]) for r in range(R + 1)]
        FK = [FK[r] + iv.mpf([-HI(TK[r]), HI(TK[r])]) for r in range(R + 1)]
        def cell(F, S, m):     # enclosure of F^{(m)} on the cell
            s = iv.mpf(0)
            for i2 in range(R + 1 - m):
                s = s + F[m + i2] * h ** i2 / fact[i2]
            e = R + 1 - m
            return s + S * iv.mpf([-1, 1]) * (w / 2) ** e / fact[e]
        r0, r1, r2 = cell(Fr, Sr, 0), cell(Fr, Sr, 1), cell(Fr, Sr, 2)
        k0, k1, k2 = cell(FK, SK, 0), cell(FK, SK, 1), cell(FK, SK, 2)
        assert LO(r0) > 0 and LO(k0) > 0, (i, r0, k0)
        fc = iv.log(Fr[0]) - iv.log(FK[0])
        f1 = Fr[1] / Fr[0] - FK[1] / FK[0]
        f2 = (r2 / r0 - (r1 / r0) ** 2) - (k2 / k0 - (k1 / k0) ** 2)
        enc = fc + f1 * h + f2 * iv.mpf([0, HI((w / 2) ** 2 / 2)])
        u = max(abs(LO(enc)), abs(HI(enc)))
        if u > up: up = u; argmax = float(LO(th))
        l0 = min(abs(LO(fc)), abs(HI(fc))) if LO(fc) * HI(fc) > 0 else mpf(0)
        if l0 > lo: lo = l0
    return dict(n=n, t_nominal=t_nominal, beta=str(beta), t_n=[float(LO(tn)), float(HI(tn))], KC=KC, KMAX=KMAX, G=G,
                delta_upper=float(up * (1 + mpf('1e-12'))), delta_lower=float(lo * (1 - mpf('1e-12'))),
                theta_at_upper=argmax, tail_rho0=float(HI(Tr[0])), tail_K0=float(HI(TK[0])), seconds=time.time() - t0)

if __name__ == '__main__':
    fl = {(r['n'], r['t']): r['beta'] for r in json.load(open('chain_float.json'))}
    out = []
    for t in (1.0, 0.5):
        for n in (4, 16, 64):
            beta = mp.nstr(mpf(fl[(n, t)]), 15)
            r = certify(n, t, beta)
            out.append(r)
            print(json.dumps(r), flush=True)
            json.dump(out, open('chain_cert.json', 'w'), indent=1)
