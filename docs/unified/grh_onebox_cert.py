#!/usr/bin/env python3
"""GRH one-box certificate: rigorous positivity of Weil's form for zeta at one support where only 2 and 3 enter.

Statement certified (see docs/unified/GRH-ONEBOX-CERT.md): for a fixed a with log 3 < 2a < log 4 and every f in
L^2(-a, a) (real or complex),

    W(f) = POLE + REAL - sum_{p=2,3} log(p) p^{-1/2} [h(log p) + h(-log p)]  >=  c ||f||^2,    c > 0 explicit,

in the conventions of docs/rh-guide/grh/weil_numerics.py (h = f * f~, F(r) = int f e^{irx} dx,
POLE = 2 Re F(i/2) conj F(-i/2), REAL = -log(pi) h(0) + (1/2pi) int |F|^2 Re psi(1/4 + ir/2) dr).  All other prime
powers p^k have k log p >= 2a and their terms vanish identically, so W is the full Weil form at this support.

Method (all arithmetic in Arb ball arithmetic via python-flint; every number below is a rigorous enclosure):
  1. Gram matrix of W on Poly_N (orthonormal Legendre p_0..p_{N-1} on [-a, a]) and the coupling block to p_N..p_{M-1},
     computed in x-space.  The real place in x-space (derived from the integral formula for psi):
       REAL(f) = c0 h(0) + int_0^{2a} (h(0) - Re h(t))/t dt - int_0^{2a} S(t) K(t) dt,
       c0 = -log(pi) - gamma - log(4a),  S(t) = h(t) + h(-t),  K(t) = e^{-t/2}/(1 - e^{-2t}) - 1/(2t)  (analytic, |t| < pi).
     K is replaced by its Taylor polynomial K_D at t = a with a Cauchy remainder bound eps_D; then every integrand is a
     polynomial and Gauss-Legendre quadrature with enough nodes is exact (rigorous nodes from Arb).
  2. Schur step.  Write f = u + g, u in Poly_N, g orthogonal to Poly_N.  Then
       W(f) >= W(u) - 2 ||Q_N H u|| ||g|| + mu ||g||^2,
     where H is the operator of W and mu is a lower bound for W on the orthogonal complement of Poly_N.
     ||Q_N H u||^2 = ||(P_M - P_N) H u||^2 + ||Q_M H u||^2.  The first is the coupling block (exact).  For M >= N + D + 1
     the second is the Legendre tail of the singular part of H u only: (u/2) [log(2a/(a-x)) + log(2a/(a+x))] (real
     place) and the jumps of u(x -+ log p) (primes), plus the pole exponentials; these Gram matrices are computed
     exactly (integer Legendre coefficients against exact log moments, Gauss on the pieces of the jumps).
  3. mu from the frequency side: for g orthogonal to Poly_N, |G(r)| <= eps_N(r) ||g|| with eps_N(r)^2 =
     2a sum_{n>=N} (2n+1) j_n(ar)^2 <= 2a sum (2n+1) (ar)^{2n}/((2n+1)!!)^2, and the symbol
     phi(r) = -log(pi) + Re psi(1/4 + ir/2) - 2 c_2 cos(r log 2) - 2 c_3 cos(r log 3) is >= phi_inf(rho) - 2(c_2 + c_3)
     for |r| >= rho, since Re psi(1/4 + ir/2) increases in |r|.
  4. The matrix  G_NN - (e_K + c) I - ((1+beta)(R_M + 3 T) + (1 + 1/beta) delta^2 I)/(mu - c)  is shown positive
     definite by a Cholesky (LDL^T) factorisation in ball arithmetic with every pivot certified > 0.

Usage: py grh_onebox_cert.py A N D [rho] [c]     e.g.  py grh_onebox_cert.py 3/5 100 40
       (A as an exact fraction; M = N + D + 2.)
"""
import math
import sys
import time
from fractions import Fraction

from flint import acb, arb, arb_mat, arb_series, ctx

T0 = time.time()


def log(msg):
    print(f"{msg}  ({time.time() - T0:.1f}s)", flush=True)


# ------------------------------------------------------------------ parameters
A_FR = Fraction(sys.argv[1]) if len(sys.argv) > 1 else Fraction(3, 5)
N = int(sys.argv[2]) if len(sys.argv) > 2 else 100
D = int(sys.argv[3]) if len(sys.argv) > 3 else 40
M = N + D + 2
PREC = 200 + int(1.3 * M) + 64                          # ball radii of the Legendre recurrence grow like 2.42^n
ctx.prec = PREC
a = arb(A_FR.numerator) / A_FR.denominator
LOG2, LOG3, LOG4, LOG5 = arb(2).log(), arb(3).log(), arb(4).log(), arb(5).log()
assert (2 * a > LOG3) and (2 * a < LOG5), "need log 3 < 2a < log 5: then only the primes 2 and 3 enter"
# prime powers p^k with k log p < 2a: (2,1), (3,1), and (2,2) when 2a > log 4.  Key = p^k; value (lag, coefficient).
assert not (abs(2 * a - LOG4) < arb("1e-30")), "2a must not equal log 4"
PRIMES = [(2, LOG2), (3, LOG3)] + ([(4, LOG4)] if 2 * a > LOG4 else [])
CP = {2: LOG2 / arb(2).sqrt(), 3: LOG3 / arb(3).sqrt(), 4: LOG2 / 2}   # Lambda(n)/sqrt(n)
CSUM = sum((CP[p] for p, _ in PRIMES), arb(0))
PI = arb.pi()
EULER = arb.const_euler()
c0 = -PI.log() - EULER - (4 * a).log()
print(f"GRH one-box certificate.  a = {A_FR} = {float(A_FR)},  e^(2a) = {float((2*a).exp()):.4f}  (3 < e^(2a) < 4)")
print(f"  N = {N} (certified space Poly_N), D = {D} (Taylor degree of K), M = N + D + 2 = {M},  precision {PREC} bits")
print(f"  c0 = -log pi - gamma - log 4a = {c0.str(12)},  coefficients Lambda(n)/sqrt(n): "
      + ", ".join(f"n={p}: {CP[p].str(12)}" for p, _ in PRIMES))
print(f"  prime powers n with log n < 2a = {(2*a).str(8)}: {[p for p, _ in PRIMES]};  log 4 = {LOG4.str(8)}, "
      f"log 5 = {LOG5.str(8)} (5 and all larger n have log n >= 2a, their terms vanish)")

# ------------------------------------------------------------------ helpers
_GL = {}


def gauss(n):
    """Rigorous Gauss-Legendre nodes and weights on [-1, 1] (exact for polynomials of degree <= 2n - 1)."""
    if n not in _GL:
        xs, ws = [], []
        for k in range(n):
            x, w = arb.legendre_p_root(n, k, weight=True)
            xs.append(x)
            ws.append(w)
        _GL[n] = (xs, ws)
    return _GL[n]


def gauss_on(n, lo, hi):
    xs, ws = gauss(n)
    h = (hi - lo) / 2
    m = (hi + lo) / 2
    return [h * x + m for x in xs], [h * w for w in ws]


def legendre_rows(pts, nmax):
    """rows[n][q] = P_n(pts[q]) for n < nmax (three-term recurrence in ball arithmetic)."""
    rows = [[arb(1)] * len(pts)]
    if nmax > 1:
        rows.append(list(pts))
    for n in range(1, nmax - 1):
        p0, p1 = rows[n - 1], rows[n]
        c1 = arb(2 * n + 1) / (n + 1)
        c2 = arb(n) / (n + 1)
        rows.append([c1 * x * u - c2 * v for x, u, v in zip(pts, p1, p0)])
    return rows


def mat(rows):
    return arb_mat(rows)


def scaled_T(rows, ws):
    """Transpose of rows with column q scaled by ws[q] -> Q x n matrix."""
    return arb_mat([[r[q] * ws[q] for r in rows] for q in range(len(ws))])


def mat_to_list(Mx):
    return [[Mx[i, j] for j in range(Mx.ncols())] for i in range(Mx.nrows())]


NRM = [arb(2 * n + 1).sqrt() for n in range(M)]          # n_i = sqrt(2i+1)


# ------------------------------------------------------------------ 1. Taylor polynomial of K at t = a, remainder
def K_exact(t):
    return (-t / 2).exp() / (1 - (-2 * t).exp()) - 1 / (2 * t)


ctx.cap = D + 1
s = arb_series([a, 1], prec=D + 1)
Ks = (s * arb(-0.5)).exp() * (1 - (s * arb(-2)).exp()).inv() - (s * arb(2)).inv()
KAPPA = [Ks.coeffs()[k] for k in range(D + 1)]
R_C = arb(28) / 10                                        # Cauchy circle |t - a| = 2.8 < sqrt(a^2 + pi^2)
assert R_C < (a * a + PI * PI).sqrt()
NARC = 4000
MR = arb(0)
for k in range(NARC):
    th_mid = arb(2 * k + 1) / (2 * NARC) * 2 * PI
    rad = PI / NARC * R_C * arb("1.0001")                # covers the arc
    z = acb(a) + R_C * acb(th_mid.cos(), th_mid.sin())
    z = acb(arb(z.real.mid(), rad), arb(z.imag.mid(), rad))
    val = abs((-z / 2).exp() / (1 - (-2 * z).exp()) - 1 / (2 * z))
    MR = MR.union(val) if k else val
MR_up = arb(MR.upper())
qr = a / R_C
EPS_D = MR_up * qr ** (D + 1) / (1 - qr)                  # sup_{|t-a|<=a} |K - K_D|
log(f"[1] K Taylor at t=a to degree {D}; Cauchy circle radius 2.8, max|K| <= {MR_up.str(6)}; eps_D <= {EPS_D.str(4)}")


def K_D(t):
    v = arb(0)
    d = t - a
    for k in range(D, -1, -1):
        v = v * d + KAPPA[k]
    return v


for tt in (arb("0.05"), a + arb("0.001"), 2 * a - arb("0.01")):   # spot check K_D against K
    assert abs(K_D(tt) - K_exact(tt)) < EPS_D


# ------------------------------------------------------------------ 2. Gram block of W on Poly_N x Poly_M
Q_ETA = (N + M) // 2 + 1                                  # exact for degree <= N + M


def Sigma(tau):
    """Sigma[i][j] = H_ij(tau) + H_ji(tau), H_ij(tau) = int_{tau-1}^1 P_i(e) P_j(e - tau) de; i < N, j < M."""
    es, ws = gauss_on(Q_ETA, tau - 1, arb(1))
    Pa = legendre_rows(es, M)
    Pb = legendre_rows([e - tau for e in es], M)
    A_N = mat(Pa[:N])
    B_N = mat(Pb[:N])
    BT = scaled_T(Pb, ws)
    AT = scaled_T(Pa, ws)
    return A_N * BT + B_N * AT


Q_TAU = (N + M + D) // 2 + 2
taus, wts = gauss_on(Q_TAU, arb(0), arb(2))
U = arb_mat(N, M)
cstar = arb(0)
for q in range(Q_TAU):
    tq, wq = taus[q], wts[q]
    beta_q = wq * (1 / (2 * tq) + a * K_D(a * tq))
    cstar += wq / (2 * tq)
    U = U - Sigma(tq) * beta_q
    if q % 20 == 0:
        log(f"    tau node {q}/{Q_TAU}")
for i in range(N):
    U[i, i] = U[i, i] + cstar * arb(4) / (2 * i + 1)        # Sigma_ii(0) = 4/(2i+1)
SIG_P = {p: Sigma(L / a) for p, L in PRIMES}


def bessel_i_sph(n, z):
    return (PI / (2 * z)).sqrt() * z.bessel_i(arb(n) + arb(1) / 2)


I_HALF = [bessel_i_sph(n, a / 2) for n in range(M)]
POLE_A = [NRM[i] * (a / 2).sqrt() * 2 * (-1) ** i * I_HALF[i] for i in range(M)]   # int p_i e^{-x/2}
POLE_B = [NRM[i] * (a / 2).sqrt() * 2 * I_HALF[i] for i in range(M)]              # int p_i e^{+x/2}
G = arb_mat(N, M)
for i in range(N):
    for j in range(M):
        v = NRM[i] * NRM[j] / 2 * (U[i, j] - sum((CP[p] * SIG_P[p][i, j] for p, _ in PRIMES), arb(0)))
        v += POLE_A[i] * POLE_B[j] + POLE_B[i] * POLE_A[j]
        if i == j:
            v += c0
        G[i, j] = v
E_K = 4 * a * EPS_D                                       # |W(u) - W_D(u)| <= 4 a eps_D ||u||^2
log(f"[2] Gram block G (N x M) done; Gauss nodes: tau {Q_TAU}, eta {Q_ETA}.  G_00 = {G[0,0].str(10)}, "
    f"G_{N-1},{N-1} = {G[N-1,N-1].str(8)};  max radius {max(float(G[i,j].rad()) for i in range(N) for j in range(M)):.2e}")
# symmetry check on the square part (a consistency test of the quadrature)
asym = max(float(abs(G[i, j] - G[j, i]).upper()) for i in range(N) for j in range(i))
log(f"    symmetry |G_ij - G_ji| <= {asym:.2e} (must be ~ ball radius)")

# ------------------------------------------------------------------ 8. convention cross-check (floating point, NOT part
# of the proof): a few Gram entries recomputed from the frequency-side definition of weil_numerics.py
#   W(f) = 2 F(i/2) F(-i/2) - log(pi) h(0) + (1/2pi) int |F|^2 Re psi(1/4 + ir/2) dr - sum Lambda(n)/sqrt(n) [h(log n) + h(-log n)]
def crosscheck():
    try:
        import numpy as np
        from scipy.integrate import quad
        from scipy.special import digamma, eval_legendre, spherical_jn
        af = float(A_FR)

        def pn(n, x):
            return math.sqrt((2 * n + 1) / (2 * af)) * eval_legendre(n, x / af) if abs(x) <= af else 0.0

        def W_freq(cs):
            # f = sum_n cs[n] p_n ; F(r) = sum cs[n] sqrt(2a(2n+1)) i^n j_n(ar)
            def F2(r):
                re = im = 0.0
                for n, c in cs.items():
                    v = c * math.sqrt(2 * af * (2 * n + 1)) * spherical_jn(n, af * r)
                    k = n % 4
                    if k == 0: re += v
                    elif k == 1: im += v
                    elif k == 2: re -= v
                    else: im -= v
                return re * re + im * im
            g = lambda r: F2(r) * (math.log(1 / math.pi) + float(np.real(digamma(0.25 + 0.5j * r))))
            R, step = 12000.0, 20.0
            tot = sum(quad(g, k * step, (k + 1) * step, limit=200)[0] for k in range(int(R / step)))
            se = sum(c * math.sqrt(2 * n + 1) for n, c in cs.items() if n % 2 == 0)
            so = sum(c * math.sqrt(2 * n + 1) for n, c in cs.items() if n % 2 == 1)
            # |F|^2 ~ (2a/z^2)(se^2 sin^2 z + so^2 cos^2 z), z = ar; symbol ~ log(r/2pi): averaged tail beyond R
            tail = (se * se + so * so) / (math.pi * af) * (math.log(R / (2 * math.pi)) + 1) / R
            real = (2 * tot) / (2 * math.pi) + tail - math.log(math.pi) * 0  # -log(pi) h(0) already inside g
            f = lambda x: sum(c * pn(n, x) for n, c in cs.items())
            Fp = quad(lambda x: f(x) * math.exp(-x / 2), -af, af)[0]
            Fm = quad(lambda x: f(x) * math.exp(x / 2), -af, af)[0]
            pr = 0.0
            for p, L in PRIMES:
                Lf = float(L.mid())
                hval = quad(lambda y: f(y) * f(y - Lf), Lf - af, af)[0]
                pr += float(CP[p].mid()) * 2 * hval
            return 2 * Fp * Fm + real - pr

        for cs, label, exact in (({0: 1.0}, "G_00", G[0, 0]), ({1: 1.0}, "G_11", G[1, 1]), ({4: 1.0}, "G_44", G[4, 4]),
                                 ({0: 1.0, 2: 1.0}, "G_00+2G_02+G_22", G[0, 0] + 2 * G[0, 2] + G[2, 2])):
            wf = W_freq(cs)
            print(f"[8] cross-check {label}: frequency side (float, tail estimated) {wf:.7f}   x-space Gram {float(exact.mid()):.7f}"
                  f"   diff {wf - float(exact.mid()):.1e}")
    except Exception as e:  # the cross-check is optional
        print(f"[8] cross-check skipped: {e}")


crosscheck()

# ------------------------------------------------------------------ 3. coupling R_M = C C^T,  C = G[:, N:M]
Cb = arb_mat([[G[i, j] for j in range(N, M)] for i in range(N)])
R_M = Cb * Cb.transpose()
log("[3] coupling block R_M done")

# ------------------------------------------------------------------ 4. Legendre tail beyond M of the singular part
# 4a. log pieces: lambda_i = (p_i/2) log(2a/(a-x)) = (p_i/2) log(1/w), w = (a-x)/(2a), p_i = n_i/sqrt(2a) P_i(1-2w).
ctx.prec = int(5.3 * M) + 400                              # exact-integer Legendre coefficients ~ 2.54 bits/degree
coef = []                                                 # P_n(1-2w) = sum_k binom(n,k) binom(n+k,k) (-w)^k
for n in range(M):
    coef.append([arb((-1) ** k * math.comb(n, k) * math.comb(n + k, k)) for k in range(n + 1)] + [arb(0)] * (M - 1 - n))
Cm = arb_mat(coef)
H1 = arb_mat([[arb(1) / (k + l + 1) ** 2 for l in range(M)] for k in range(M)])      # int_0^1 w^{k+l} log(1/w)
H2 = arb_mat([[arb(2) / (k + l + 1) ** 3 for l in range(N)] for k in range(N)])      # int_0^1 w^{k+l} log^2(1/w)
CN = arb_mat([coef[n][:N] for n in range(N)])
I1 = CN * arb_mat([[H1[k, l] for l in range(M)] for k in range(N)]) * Cm.transpose()  # N x M
I2 = CN * H2 * CN.transpose()                                                       # N x N
ctx.prec = PREC
I1 = arb_mat([[arb(I1[i, j]) for j in range(M)] for i in range(N)])
I2 = arb_mat([[arb(I2[i, j]) for j in range(N)] for i in range(N)])
GramL = arb_mat([[NRM[i] * NRM[j] / 4 * I2[i, j] for j in range(N)] for i in range(N)])
ProjL = arb_mat([[NRM[i] * NRM[m] / 2 * I1[i, m] for m in range(M)] for i in range(N)])
T_L = GramL - ProjL * ProjL.transpose()
SGN = [(-1) ** i for i in range(N)]
T_R = arb_mat([[T_L[i, j] * SGN[i] * SGN[j] for j in range(N)] for i in range(N)])  # mirror x -> -x
log(f"[4a] log-piece tail Gram T_L: diag max {max(float(T_L[i,i].mid()) for i in range(N)):.3e}, "
    f"T_L[0,0] = {T_L[0,0].str(6)}")

# 4b. jump pieces: sigma_i(xi) = n_i/sqrt(2a) sum_p c_p [P_i(xi - l_p) 1(xi > l_p - 1) + P_i(xi + l_p) 1(xi < 1 - l_p)]
lam = {p: L / a for p, L in PRIMES}
bps = sorted([1 - lam[p] for p, _ in PRIMES] + [lam[p] - 1 for p, _ in PRIMES], key=lambda z: float(z.mid()))
edges = [arb(-1)] + bps + [arb(1)]
Q_J = (N + M) // 2 + 1
SigRows = [[] for _ in range(N)]
PmRows = [[] for _ in range(M)]
WJ = []
for e0, e1 in zip(edges[:-1], edges[1:]):
    xs, ws = gauss_on(Q_J, e0, e1)
    mid = float(((e0 + e1) / 2).mid())
    Pm = legendre_rows(xs, M)
    acc = [[arb(0)] * len(xs) for _ in range(N)]
    for p, _ in PRIMES:
        if mid > float((lam[p] - 1).mid()):
            sh = legendre_rows([x - lam[p] for x in xs], N)
            for i in range(N):
                acc[i] = [u + CP[p] * v for u, v in zip(acc[i], sh[i])]
        if mid < float((1 - lam[p]).mid()):
            sh = legendre_rows([x + lam[p] for x in xs], N)
            for i in range(N):
                acc[i] = [u + CP[p] * v for u, v in zip(acc[i], sh[i])]
    for i in range(N):
        SigRows[i] += [NRM[i] / (2 * a).sqrt() * v for v in acc[i]]
    for m in range(M):
        PmRows[m] += [NRM[m] / (2 * a).sqrt() * v for v in Pm[m]]
    WJ += [a * w for w in ws]                              # dx = a dxi
SigM = mat(SigRows)
GramJ = SigM * scaled_T(SigRows, WJ)
ProjJ = SigM * scaled_T(PmRows, WJ)
T_J = GramJ - ProjJ * ProjJ.transpose()
log(f"[4b] jump-piece tail Gram T_J: diag max {max(float(T_J[i,i].mid()) for i in range(N)):.3e}")


# 4c. consistency check of the singular structure: for N + D + 1 <= m, <H_D p_i, p_m> must equal the projection of
#     the singular part plus the pole part.  Only columns m < M exist here; m = M-1 = N + D + 1 is one such column.
def struct_check(m):
    worst = 0.0
    for i in range(N):
        pred = ProjL[i, m] + SGN[i] * (-1) ** m * ProjL[i, m] - ProjJ[i, m]
        pred += POLE_A[i] * POLE_B[m] + POLE_B[i] * POLE_A[m]
        worst = max(worst, float(abs(pred - G[i, m]).mid()))
    return worst


log(f"[4c] structure check, column m = {M-1}: max |G_im - (singular + pole projection)| = {struct_check(M-1):.2e} "
    f"(should be ~ eps_D-level)")

# 4d. pole tail: ||Q_M e^{+-x/2}||^2 <= 2a sum_{n>=M} (2n+1) i_n(a/2)^2, i_n(z) <= z^n cosh z/(2n+1)!!
z = a / 2


def dfact(n):
    r = arb(1)
    for k in range(1, n + 1, 2):
        r *= k
    return r


tM = z ** M * z.cosh() / dfact(2 * M + 1)
ratio = (z / (2 * M + 1)) ** 2                            # bounds the ratio of consecutive terms (2n+1) i_n^2
EPS_E2 = 2 * a * (2 * M + 1) * tM ** 2 / (1 - ratio)
EPS_E = EPS_E2.sqrt()
NORM_E = ((a).sinh() * 2).sqrt()                            # ||e^{+-x/2}||_{L2(-a,a)} = sqrt(2 sinh a)
DELTA = 2 * a * EPS_D + EPS_E * 2 * NORM_E
log(f"[4d] ||Q_M e^(+-x/2)|| <= {EPS_E.str(3)};  delta (analytic remainder) <= {DELTA.str(3)}")

# ------------------------------------------------------------------ 5. mu: lower bound of W on (Poly_N)^perp


def phi_inf(r):
    return -PI.log() + acb(arb(1) / 4, r / 2).digamma().real


def mu_at(rho):
    zr = a * rho
    if not float(zr.upper()) < 2 * N + 3:
        return None
    term = zr ** (2 * N) / dfact(2 * N + 1) ** 2
    eta = 2 * a / PI * rho * term / (1 - (zr / (2 * N + 3)) ** 2)
    phimin = phi_inf(rho) - 2 * CSUM
    return phimin * (1 - eta) - PHI_NEG * eta - 2 * EPS_EN ** 2, eta, phimin


PHI_NEG = -(phi_inf(arb(0)) - 2 * CSUM)        # max of phi^- over all r (phi_inf increasing in |r|)
tN = z ** N * z.cosh() / dfact(2 * N + 1)
EPS_EN = (2 * a * (2 * N + 1) * tN ** 2 / (1 - (z / (2 * N + 1)) ** 2)).sqrt()
if len(sys.argv) > 4 and sys.argv[4] != "auto":
    RHO = arb(sys.argv[4])
else:                                                     # pick rho on a grid to maximise the certified mu
    best = None
    for k in range(40, 100):
        rho = arb(int(k / 100 * N / float(A_FR)))
        r = mu_at(rho)
        if r is not None and (best is None or r[0].lower() > best[1].lower()):
            best = (rho, r[0])
    RHO = best[0]
MU, ETA, PHI_MIN = mu_at(RHO)
log(f"[5] rho = {RHO.str(6)}: phi_inf(rho) = {phi_inf(RHO).str(8)}, phi_min = {PHI_MIN.str(8)}, eta <= {ETA.str(3)}, "
    f"max phi^- = {PHI_NEG.str(6)},  ||Q_N e^(+-x/2)|| <= {EPS_EN.str(3)};  mu >= {MU.str(8)}")
assert MU > 0

# ------------------------------------------------------------------ 6. the final matrix and its Cholesky
G_NN = arb_mat([[G[i, j] for j in range(N)] for i in range(N)])
# symmetrise (both triangles enclose the same exact value; take the intersection-free union for safety)
G_NN = arb_mat([[G_NN[i, j].union(G_NN[j, i]) for j in range(N)] for i in range(N)])
T_ALL = T_L + T_R + T_J
if len(sys.argv) > 6:                                     # optional dump of midpoints for diagnostics (not part of the proof)
    import json
    dmp = {k: [[Mx[i, j].mid().str(60, radius=False) for j in range(N)] for i in range(N)]
           for k, Mx in (("G", G_NN), ("R", R_M), ("TL", T_L), ("TR", T_R), ("TJ", T_J))}
    dmp["mu"] = MU.mid().str(30, radius=False)
    json.dump(dmp, open(sys.argv[6], "w"))
BETA = arb("1e-6")


VERBOSE = False


def ldl_min_pivot(S):
    n = S.nrows()
    Lm = [[arb(0)] * n for _ in range(n)]
    d = [arb(0)] * n
    for j in range(n):
        v = S[j, j] - sum((Lm[j][k] * Lm[j][k] * d[k] for k in range(j)), arb(0))
        if not v > 0:
            if VERBOSE:
                print(f"    pivot {j}: v = {v.str(6)}, S_jj = {S[j, j].str(6)}, G_jj = {G_NN[j, j].str(6)}, "
                      f"R_jj = {R_M[j, j].str(6)}, T_jj = {T_ALL[j, j].str(6)}")
            return None, j
        d[j] = v
        for i in range(j + 1, n):
            Lm[i][j] = (S[i, j] - sum((Lm[i][k] * Lm[j][k] * d[k] for k in range(j)), arb(0))) / v
    return d, n


def final_matrix(c):
    Rt = (R_M + T_ALL * 3) * (1 + BETA)
    S = G_NN - Rt * (1 / (MU - c))
    shift = E_K + c + (1 + 1 / BETA) * DELTA ** 2 / (MU - c)
    for i in range(N):
        S[i, i] = S[i, i] - shift
    return S




def certify(c):
    d, j = ldl_min_pivot(final_matrix(c))
    return d


# smallest c that fails / largest that passes, by bisection in log scale (LDL in ball arithmetic is the test)
if len(sys.argv) > 5:
    c_ok = arb(sys.argv[5]) if certify(arb(sys.argv[5])) is not None else None
else:
    lo, hi = -40.0, -5.0                                  # log10 c
    if certify(arb(f"1e{int(lo)}")) is None:
        c_ok = None
    else:
        for _ in range(14):
            mid = (lo + hi) / 2
            if certify(arb(f"{10 ** mid:.6e}")) is not None:
                lo = mid
            else:
                hi = mid
        c_ok = arb(f"{10 ** lo:.4e}")
if c_ok is None:
    log("[6] Cholesky FAILED: positivity NOT certified with these parameters")
    sys.exit(1)
d = certify(c_ok)
dmin = min(d, key=lambda v: float(v.lower()))
log(f"[6] CERTIFIED: LDL^T of the final matrix with c = {c_ok.str(4)} succeeds, all {N} pivots > 0 "
    f"(smallest pivot in {dmin.str(4)}).")

# ------------------------------------------------------------------ 7. upper bound: Rayleigh quotient on Poly_N
# Inverse iteration on G_NN (midpoints, not rigorous) gives a trial vector u; its Rayleigh quotient is then evaluated
# in ball arithmetic.  W(u) <= u^T G_NN u + 4a eps_D ||u||^2, so this is a rigorous upper bound for inf W/||f||^2.
Gm = [[arb(G_NN[i, j].mid()) for j in range(N)] for i in range(N)]
Lm = [[arb(0)] * N for _ in range(N)]
dd = [arb(0)] * N
for j in range(N):
    v = Gm[j][j] - sum((Lm[j][k] * Lm[j][k] * dd[k] for k in range(j)), arb(0))
    dd[j] = arb(v.mid())
    for i in range(j + 1, N):
        Lm[i][j] = arb(((Gm[i][j] - sum((Lm[i][k] * Lm[j][k] * dd[k] for k in range(j)), arb(0))) / dd[j]).mid())
u = [arb(1)] * N
for it in range(4):
    y = [arb(0)] * N
    for i in range(N):
        y[i] = arb((u[i] - sum((Lm[i][k] * y[k] for k in range(i)), arb(0))).mid())
    y = [arb((y[i] / dd[i]).mid()) for i in range(N)]
    x = [arb(0)] * N
    for i in range(N - 1, -1, -1):
        x[i] = arb((y[i] - sum((Lm[k][i] * x[k] for k in range(i + 1, N)), arb(0))).mid())
    nrm = max(abs(float(t.mid())) for t in x)
    u = [arb((t / nrm).mid()) for t in x]
uv = arb_mat([[t] for t in u])
num = (uv.transpose() * G_NN * uv)[0, 0]
den = (uv.transpose() * uv)[0, 0]
RQ = num / den + E_K
log(f"[7] Rayleigh quotient of a trial polynomial (degree < {N}): inf W(f)/||f||^2 <= {RQ.str(6)}")
print("")
print(f"RESULT  a = {A_FR}:  {c_ok.str(4)} * ||f||^2  <=  W(f)  for every f in L^2(-{A_FR}, {A_FR}) (real or complex),")
print(f"        and inf_f W(f)/||f||^2 <= {RQ.str(5)}  (attained up to this by a polynomial).")
print(f"        inputs: N = {N}, D = {D}, M = {M}, rho = {RHO.str(6)}, mu >= {MU.str(6)}, eps_D <= {EPS_D.str(3)}, "
      f"delta <= {DELTA.str(3)}, eta <= {ETA.str(3)}")

