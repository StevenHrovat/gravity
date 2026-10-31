"""GUID v6: Our theory as simulated. The spin entanglement witness of the Bose-Mazumdar-Morley-Ulbricht-Toros-Paternostro-Geraci-Barker-
Kim-Milburn proposal (Phys. Rev. Lett. 119, 240401 (2017); arXiv:1707.06050, the only arXiv version, v1 of 19 July 2017), checked and
corrected. Every number the simulation paper may quote is computed here and written to results/bmv_witness.json.

Run: python3 docs/simulation/bmv_witness.py   (numpy, scipy; deterministic, fixed seeds; under a minute).
Each check prints OK or FAIL with got and expected; the last line counts them; the exit code is 0 only if all pass.

The state at the end of the two Stern-Gerlach interferometers (arXiv:1707.06050, the unnumbered equation after Eq. (6)), overall phase
omitted, |up> = |0>, |down> = |1>:
    |Psi> = (1/2) [ |00> + e^{i a} |01> + e^{i b} |10> + |11> ],   a = Delta phi_LR, b = Delta phi_RL,   Sigma = a + b.
The paper's witness, as printed: W = |<sx (x) sz> - <sy (x) sz>|, "If W is found to exceed unity then the state is proven to be entangled".

  [B1] the printed witness: sx (x) sz - sy (x) sz = sqrt2 s_n (x) sz with n = (x - y)/sqrt2, so product states reach sqrt2 (analytic,
       random sampling, optimiser); its values on the proposal's own states
  [B2] valid witnesses: the two-pair lemma |<s_a1 s_b1> + <s_a2 s_b2>| <= 1 (a1 perp a2, b1 perp b2) for every separable state; the
       corrected witness in the symmetric gauge W_c = |<sx sx> + <sy sz>| = 1 + sin(Sigma/2) and its lab-gauge axes; the gauge-free
       trace-norm criterion ||T||_1 <= 1 with ||T||_1 = 1 + 2 sin(Sigma/2); the variant |<sx sz> + <sy sy>| and why it is weak
  [B3] under independent dephasing at lambda per mass (the Diosi-Penrose rate of Bridge B) with entangling rate omega (Sigma = omega t):
       the thresholds in omega/lambda of the negativity (2), the trace norm (2), W_c (4) and the best two-pair witness (3.806, which
       switches to |<sy sz> + <sz sy>| = 2 e^{-lambda t} sin(omega t/2) at a finite time; closed form)
  [B4] experimental runs needed: the unbiased two-setting estimator of W_c, n >= k^2 cot^2(Sigma/2) runs per setting; the upward bias of the
       estimated trace norm on a product state (Monte Carlo)
"""

import json
import math
import platform
import sys
import time
from pathlib import Path

import numpy as np
import scipy
from scipy import optimize

T_START = time.perf_counter()
OUT = Path(__file__).resolve().parent / "results" / "bmv_witness.json"
results = []
RES = {"meta": {}, "checks": []}


def check(label, got, want, rtol=1e-6, atol=0.0):
    got, want = float(got), float(want)
    ok = abs(got - want) <= max(atol, rtol * abs(want))
    print(f"{'OK  ' if ok else 'FAIL'} {label}: {got:.6g} (expected {want:.6g})", flush=True)
    results.append(ok)
    RES["checks"].append({"label": label, "ok": ok, "got": got, "expected": want, "rtol": rtol, "atol": atol})


def check_true(label, cond):
    ok = bool(cond)
    print(f"{'OK  ' if ok else 'FAIL'} {label}", flush=True)
    results.append(ok)
    RES["checks"].append({"label": label, "ok": ok})


I2 = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], complex)
Y = np.array([[0, -1j], [1j, 0]])
Z = np.diag([1.0, -1.0]).astype(complex)
PAULI = (X, Y, Z)


def ket_bmv(a, b):
    return np.array([1, np.exp(1j * a), np.exp(1j * b), 1], complex) / 2


def dm(psi):
    return np.outer(psi, psi.conj())


def corr(rho):
    """Correlation matrix T_ij = <s_i (x) s_j>, rows qubit 1 (x, y, z), columns qubit 2."""
    return np.array([[np.trace(rho @ np.kron(A, B)).real for B in PAULI] for A in PAULI])


def ev(rho, op):
    return float(np.trace(rho @ op).real)


def negativity(rho):
    pt = rho.reshape(2, 2, 2, 2).transpose(0, 3, 2, 1).reshape(4, 4)
    w = np.linalg.eigvalsh(pt)
    return float(-w[w < 0].sum())


def axis_op(n):
    return n[0] * X + n[1] * Y + n[2] * Z


def prod_max_sampled(Wop, n=400_000, seed=11):
    """Largest |<W>| over n random product pure states (Bloch vectors uniform on the sphere)."""
    rng = np.random.default_rng(seed)
    a = rng.normal(size=(n, 3))
    a /= np.linalg.norm(a, axis=1)[:, None]
    b = rng.normal(size=(n, 3))
    b /= np.linalg.norm(b, axis=1)[:, None]
    # <A (x) B> on a product state = sum_ij a_i b_j T^W_ij with T^W_ij = tr(W s_i s_j)/4
    TW = np.array([[np.trace(Wop @ np.kron(A, B)).real / 4 for B in PAULI] for A in PAULI])
    return float(np.max(np.abs(np.einsum("ni,ij,nj->n", a, TW, b))))


def prod_max_opt(Wop, starts=40, seed=7):
    """Largest |<W>| over product pure states, Nelder-Mead from seeded starts."""
    def ket(t, p):
        return np.array([math.cos(t / 2), math.sin(t / 2) * np.exp(1j * p)])

    def f(x):
        v = np.kron(ket(x[0], x[1]), ket(x[2], x[3]))
        return -abs(np.vdot(v, Wop @ v).real)

    rs = np.random.default_rng(seed)
    return max(-optimize.minimize(f, rs.uniform(0, np.pi, 4) * np.array([1, 2, 1, 2]), method="Nelder-Mead",
                                  options=dict(xatol=1e-12, fatol=1e-14, maxiter=6000)).fun for _ in range(starts))


RES["meta"] = {"python": platform.python_version(), "numpy": np.__version__, "scipy": scipy.__version__,
               "source": "arXiv:1707.06050 v1 (19 Jul 2017), accepted-manuscript text; PRL 119, 240401 (2017) not read",
               "state": "(1/2)[|00> + e^{ia}|01> + e^{ib}|10> + |11>], a = Delta phi_LR, b = Delta phi_RL, |up> = |0>"}

# =================================================================================================================================
print("[B1] The printed witness W = |<sx sz> - <sy sz>|")
B1 = RES["B1"] = {}
W_print = np.kron(X, Z) - np.kron(Y, Z)
n_diag = np.array([1.0, -1.0, 0.0]) / math.sqrt(2)
check("operator identity: sx sz - sy sz = sqrt2 s_n sz, n = (x - y)/sqrt2 (max entry of the difference)",
      np.abs(W_print - math.sqrt(2) * np.kron(axis_op(n_diag), Z)).max(), 0.0, atol=1e-15)
# the counterexample: qubit 1 along n, qubit 2 up
v1 = np.linalg.eigh(axis_op(n_diag))[1][:, 1]
ce = np.kron(v1, np.array([1, 0], complex))
w_ce = ev(dm(ce), W_print)
check("product state (qubit 1 Bloch vector (1, -1, 0)/sqrt2, qubit 2 up) gives W = sqrt2", w_ce, math.sqrt(2), rtol=1e-12)
check("its negativity is 0 (a product state)", negativity(dm(ce)), 0.0, atol=1e-15)
ps = prod_max_sampled(W_print)
po = prod_max_opt(W_print)
check_true(f"400 000 random product states reach {ps:.4f} (> 1)", ps > 1.39)
check("maximum over product states (optimiser, 40 starts) = sqrt2", po, math.sqrt(2), rtol=1e-8)
# the proposal's own states: the printed witness over a grid of (a, b)
grid = np.linspace(0, 2 * np.pi, 361)
Wv = np.array([[abs(ev(dm(ket_bmv(a, b)), W_print)) for b in grid] for a in grid])
ia, ib = np.unravel_index(Wv.argmax(), Wv.shape)
B1.update({"product_max_sampled": ps, "product_max_opt": po, "counterexample_W": w_ce,
           "max_on_bmv_states": float(Wv.max()), "argmax_a": float(grid[ia]), "argmax_b": float(grid[ib])})
check("largest printed W on the proposal's states over all (a, b): the separable value sqrt2 is never exceeded", Wv.max(),
      math.sqrt(2), rtol=1e-3)
for a, b in ((0.0, 1.0), (0.5, 0.5), (0.0, math.pi / 2), (0.0, math.pi)):
    B1[f"W_print(a={a:.4f},b={b:.4f})"] = ev(dm(ket_bmv(a, b)), W_print)
check("example: a = 0, b = 1 rad (the paper's Sigma ~ O(1), inner branches closest): printed W = 0.65, below 1 though the state is entangled",
      abs(B1["W_print(a=0.0000,b=1.0000)"]), 0.6506, rtol=1e-3)

# =================================================================================================================================
print("\n[B2] Valid witnesses")
B2 = RES["B2"] = {}
# the two-pair lemma: for unit a1 perp a2, b1 perp b2 and a product state with Bloch vectors u, v:
# |(u.a1)(v.b1) + (u.a2)(v.b2)| <= sqrt((u.a1)^2 + (u.a2)^2) sqrt((v.b1)^2 + (v.b2)^2) <= 1 (Cauchy-Schwarz), and convexity.
rng = np.random.default_rng(3)
lemma_max = 0.0
for _ in range(25):
    q1, _r = np.linalg.qr(rng.normal(size=(3, 3)))
    q2, _r = np.linalg.qr(rng.normal(size=(3, 3)))
    Wop = np.kron(axis_op(q1[:, 0]), axis_op(q2[:, 0])) + np.kron(axis_op(q1[:, 1]), axis_op(q2[:, 1]))
    lemma_max = max(lemma_max, prod_max_opt(Wop, starts=12))
check("two-pair lemma: 25 random orthogonal axis pairs, largest product-state value = 1", lemma_max, 1.0, rtol=1e-7)
W_c = np.kron(X, X) + np.kron(Y, Z)
check("corrected witness W_c = |<sx sx> + <sy sz>|: maximum over product states = 1", prod_max_opt(W_c), 1.0, rtol=1e-8)
W_var = np.kron(X, Z) + np.kron(Y, Y)
check("variant |<sx sz> + <sy sy>|: maximum over product states = 1 (valid)", prod_max_opt(W_var), 1.0, rtol=1e-8)

Sig = np.linspace(0.0, np.pi, 181)[1:]
wc_sym = np.array([ev(dm(ket_bmv(s / 2, s / 2)), W_c) for s in Sig])
check("symmetric gauge a = b = Sigma/2: W_c = 1 + sin(Sigma/2) for Sigma in (0, pi] (max deviation)",
      np.abs(wc_sym - (1 + np.sin(Sig / 2))).max(), 0.0, atol=1e-13)
neg_sym = np.array([negativity(dm(ket_bmv(s / 2, s / 2))) for s in Sig])
check("negativity = sin(Sigma/2)/2 (max deviation), so W_c - 1 = 2 x negativity on these pure states",
      np.abs(neg_sym - np.sin(Sig / 2) / 2).max(), 0.0, atol=1e-13)


def lab_witness(a, b):
    """W_c rotated into the lab gauge: theta = (a - b)/2; qubit 1 axes x' = cos th x - sin th y, y' = sin th x + cos th y;
    qubit 2 axis x'' = cos th x + sin th y; z unchanged."""
    th = (a - b) / 2
    A1 = math.cos(th) * X - math.sin(th) * Y
    A2 = math.sin(th) * X + math.cos(th) * Y
    B1_ = math.cos(th) * X + math.sin(th) * Y
    return np.kron(A1, B1_) + np.kron(A2, Z)


dev = 0.0
for a in np.linspace(-np.pi, np.pi, 25):
    for b in np.linspace(-np.pi, np.pi, 25):
        dev = max(dev, abs(ev(dm(ket_bmv(a, b)), lab_witness(a, b)) - (1 + math.sin((a + b) / 2))))
check("lab gauge (any a, b in [-pi, pi]): axes rotated by theta = (Delta phi_LR - Delta phi_RL)/2 give <W_c> = 1 + sin((a + b)/2), "
      "Sigma not reduced mod 2pi (a shift of a by 2pi flips the sign of both x axes) (max deviation)", dev, 0.0, atol=1e-12)
# the axes are local data: the single-spin Bloch vectors point along the rotated x axes
a0, b0 = 0.0, 1.0
rho0 = dm(ket_bmv(a0, b0))
bl1 = [ev(rho0, np.kron(P, I2)) for P in PAULI]
bl2 = [ev(rho0, np.kron(I2, P)) for P in PAULI]
th0 = (a0 - b0) / 2
check("calibration from local data: qubit 1 Bloch vector = cos(Sigma/2) (cos th, -sin th, 0) (max deviation, a = 0, b = 1)",
      np.abs(np.array(bl1) - math.cos((a0 + b0) / 2) * np.array([math.cos(th0), -math.sin(th0), 0])).max(), 0.0, atol=1e-13)
check("qubit 2 Bloch vector = cos(Sigma/2) (cos th, sin th, 0) (max deviation)",
      np.abs(np.array(bl2) - math.cos((a0 + b0) / 2) * np.array([math.cos(th0), math.sin(th0), 0])).max(), 0.0, atol=1e-13)
# trace norm: gauge-free
tn_dev, tn_gauge = 0.0, 0.0
for s in Sig[::10]:
    tn = np.linalg.svd(corr(dm(ket_bmv(s / 2, s / 2))), compute_uv=False).sum()
    tn_dev = max(tn_dev, abs(tn - (1 + 2 * math.sin(s / 2))))
    for a in np.linspace(-2, 2, 9):
        tn_gauge = max(tn_gauge, abs(np.linalg.svd(corr(dm(ket_bmv(a, s - a))), compute_uv=False).sum() - tn))
check("trace norm ||T||_1 = 1 + 2 sin(Sigma/2) (max deviation)", tn_dev, 0.0, atol=1e-12)
check("and it does not depend on the gauge a - b (max deviation over 9 gauges per Sigma)", tn_gauge, 0.0, atol=1e-12)
rs = np.random.default_rng(5)
tn_prod = 0.0
for _ in range(2000):
    u = rs.normal(size=(2, 3)); u /= np.linalg.norm(u, axis=1)[:, None]
    tn_prod = max(tn_prod, np.linalg.svd(np.outer(u[0], u[1]), compute_uv=False).sum())
check("trace norm of a product state = |u||v| = 1 (2000 random product states, max)", tn_prod, 1.0, rtol=1e-12)
# best two-pair witness = sum of the two largest singular values
s2 = np.array([np.linalg.svd(corr(dm(ket_bmv(0.0, s))), compute_uv=False)[:2].sum() for s in Sig])
check("best two-pair witness on the proposal's states = 1 + sin(Sigma/2), any gauge (max deviation)",
      np.abs(s2 - (1 + np.sin(Sig / 2))).max(), 0.0, atol=1e-12)
# the variant |<xz> + <yy>| in the paper's geometry (a ~ 0) and in the symmetric gauge
var_a0 = np.array([ev(dm(ket_bmv(0.0, s)), W_var) for s in Sig])
check("variant in the paper's geometry (a = 0): |<sx sz> + <sy sy>| = 1 - cos(Sigma) (max deviation)",
      np.abs(np.abs(var_a0) - (1 - np.cos(Sig))).max(), 0.0, atol=1e-13)
var_sym = np.array([ev(dm(ket_bmv(s / 2, s / 2)), W_var) for s in Sig])
check("variant in the symmetric gauge: 0 for every Sigma (max |value|)", np.abs(var_sym).max(), 0.0, atol=1e-13)
B2.update({"two_pair_lemma_max": lemma_max, "W_c_formula": "1 + sin(Sigma/2)", "trace_norm_formula": "1 + 2 sin(Sigma/2)",
           "variant_formula_paper_geometry": "1 - cos(Sigma), detects only Sigma > pi/2",
           "at_Sigma_1rad": {"W_c": 1 + math.sin(0.5), "trace_norm": 1 + 2 * math.sin(0.5), "variant_a0": 1 - math.cos(1.0),
                             "printed_a0": B1["W_print(a=0.0000,b=1.0000)"], "negativity": math.sin(0.5) / 2}})

# =================================================================================================================================
print("\n[B3] Under dephasing at lambda per mass (Bridge B), entangling rate omega, Sigma = omega t")
B3 = RES["B3"] = {}
S4 = [(0, 0), (0, 1), (1, 0), (1, 1)]
hd = np.array([[abs(p[0] - q[0]) + abs(p[1] - q[1]) for q in S4] for p in S4])   # Hamming distance of branches


def rho_t(r, t):
    """lambda = 1, omega = r: the entangling phase on |10> (paper geometry, a = 0), coherence e^{-lambda t} per differing mass."""
    psi = ket_bmv(0.0, r * t)
    return dm(psi) * np.exp(-t * hd)


ts = np.concatenate([np.geomspace(1e-6, 1e-1, 400), np.linspace(0.1, 12.0, 1200)])


def refine(f, grid):
    """Maximum of f over t: every local maximum of the grid values is refined by a bounded scalar search between its neighbours
    (near a threshold the edge t -> 0 and an interior maximum can compete, and the interior one falls between grid points)."""
    vals = np.array([f(t) for t in grid])
    best_v = float(vals.max())
    n = grid.size
    for k in range(n):
        if vals[k] >= vals[max(k - 1, 0)] and vals[k] >= vals[min(k + 1, n - 1)]:
            lo, hi = grid[max(k - 1, 0)], grid[min(k + 1, n - 1)]
            res = optimize.minimize_scalar(lambda t: -f(t), bounds=(lo, hi), method="bounded", options=dict(xatol=1e-12))
            best_v = max(best_v, float(-res.fun))
    return best_v


def best(r, kind):
    def f(t):
        rho = rho_t(r, t)
        if kind == "neg":
            return negativity(rho)
        sv = np.linalg.svd(corr(rho), compute_uv=False)
        return (sv.sum() if kind == "tn" else sv[:2].sum()) - 1
    return refine(f, ts)


def bisect(fun, lo, hi, it=40):
    for _ in range(it):
        mid = 0.5 * (lo + hi)
        lo, hi = (lo, mid) if fun(mid) > 1e-12 else (mid, hi)
    return 0.5 * (lo + hi)


# dephased correlation matrix in the symmetric gauge: T = [[q^2, 0, 0], [0, 0, q s], [0, q s, 0]], q = e^{-lambda t}, s = sin(omega t/2):
# <xx> lives on the Hamming-2 coherences (q^2), <yz> and <zy> on the Hamming-1 coherences (q). Singular values q^2, q s, q s.
t_ = 0.37
Tq = corr(rho_t(3.0, t_))
svq = np.sort(np.linalg.svd(Tq, compute_uv=False))[::-1]
want = np.sort([math.exp(-2 * t_), math.exp(-t_) * math.sin(1.5 * t_), math.exp(-t_) * math.sin(1.5 * t_)])[::-1]
check("dephased singular values = (e^{-2 lambda t}, e^{-lambda t} sin(omega t/2) twice) (omega = 3 lambda, t = 0.37/lambda, max deviation)",
      np.abs(svq - want).max(), 0.0, atol=1e-13)


def best_fixed(r, kind):
    if kind == "Wc":
        return refine(lambda t: math.exp(-2 * t) + math.exp(-t) * math.sin(r * t / 2) - 1, ts)
    return refine(lambda t: 2 * math.exp(-t) * math.sin(r * t / 2) - 1, ts)


th_neg = bisect(lambda r: best(r, "neg"), 0.5, 6.0)
th_tn = bisect(lambda r: best(r, "tn"), 0.5, 6.0)
th_2p = bisect(lambda r: best(r, "2p"), 0.5, 8.0)
th_wc = bisect(lambda r: best_fixed(r, "Wc"), 0.5, 8.0)
th_yz = bisect(lambda r: best_fixed(r, "yz"), 0.5, 8.0)
# closed form for |<yz> + <zy>| = 2 q s: with u = omega/(2 lambda) the maximum over t sits at tan(u lambda t) = u, value
# 2 u e^{-arctan(u)/u} / sqrt(1 + u^2); the threshold solves value = 1
u_star = optimize.brentq(lambda u: 2 * u * math.exp(-math.atan(u) / u) / math.sqrt(1 + u * u) - 1, 0.5, 5.0, xtol=1e-14)
check("negativity threshold omega/lambda (reproduces gravity_simulated.py G2)", th_neg, 2.0, rtol=1e-4)
check("trace-norm criterion threshold omega/lambda: as tight as the negativity (first order q^2 + 2 q s = 1 + (omega - 2 lambda) t)",
      th_tn, 2.0, rtol=1e-4)
check("W_c = |<xx> + <yz>| (symmetric gauge) threshold: 4 (first order q^2 + q s = 1 + (omega/2 - 2 lambda) t)", th_wc, 4.0, rtol=1e-4)
check("|<yz> + <zy>| threshold = 2 u*, u* from the closed form (maximum at a finite time, not at t -> 0)", th_yz, 2 * u_star, rtol=1e-5)
check("best two-pair witness (axes re-optimised at every t) threshold = min(4, 2 u*) = 2 u*", th_2p, 2 * u_star, rtol=1e-5)
B3.update({"threshold_negativity": th_neg, "threshold_trace_norm": th_tn, "threshold_two_pair": th_2p, "threshold_W_c": th_wc,
           "threshold_yz_plus_zy": th_yz, "threshold_yz_plus_zy_closed_form": 2 * u_star,
           "bose_instance_rho": 1.745e-3, "note": "every two-sphere geometry has omega/lambda <= 1 (gravity_simulated.py G2), below every threshold here"})

# =================================================================================================================================
print("\n[B4] Runs needed (no decoherence)")
B4 = RES["B4"] = {}


def runs_per_setting(S, k):
    """Two settings, n runs each; <A1 B1> = 1 has no shot noise on the pure state, <A2 B2> = sin(S/2) has variance cos^2(S/2)/n."""
    return math.ceil(k * k / math.tan(S / 2) ** 2)


for S in (1.0, math.pi / 2, 1e-2, 1e-4):
    for k in (3, 5):
        B4[f"Sigma={S:g},k={k}"] = runs_per_setting(S, k)
check("Sigma = 1 rad, 5 sigma: runs per setting = ceil(25 cot^2(1/2))", B4["Sigma=1,k=5"], math.ceil(25 / math.tan(0.5) ** 2), rtol=0)
check("Sigma = 1e-4 rad (the paper's 'modest' variant), 3 sigma: about 3.6e9 runs per setting", B4["Sigma=0.0001,k=3"], 3.6e9, rtol=1e-3)
# Monte Carlo of the two-setting estimator at Sigma = 1 rad
rngm = np.random.default_rng(17)
nrun = B4["Sigma=1,k=5"]
rho1 = dm(ket_bmv(0.5, 0.5))
p1 = (1 + ev(rho1, np.kron(X, X))) / 2
p2 = (1 + ev(rho1, np.kron(Y, Z))) / 2
est = (2 * rngm.binomial(nrun, p1, 20000) / nrun - 1) + (2 * rngm.binomial(nrun, p2, 20000) / nrun - 1)
zs = (est - 1) / est.std()
check("Monte Carlo (20000 experiments of 2 x n runs, Sigma = 1): mean estimate = 1 + sin(1/2)", est.mean(), 1 + math.sin(0.5), rtol=2e-3)
check_true(f"... and the mean significance (W - 1)/sd is at least 5 ({zs.mean():.2f})", zs.mean() >= 5)
# trace norm bias on the product state |++> (T = diag(1, 0, 0)): 9 settings, n runs each
tnb = {}
for n in (100, 1000, 10000):
    Tt = np.zeros((3, 3))
    T0 = np.diag([1.0, 0.0, 0.0])
    vals = []
    for _ in range(2000):
        Th = 2 * rngm.binomial(n, (1 + T0) / 2) / n - 1
        vals.append(np.linalg.svd(Th, compute_uv=False).sum())
    tnb[n] = float(np.mean(vals) - 1)
check_true(f"estimated trace norm on a product state is biased upward: +{tnb[100]:.3f}, +{tnb[1000]:.3f}, +{tnb[10000]:.4f} at n = 100, "
           f"1000, 10000 runs per setting (so it needs a calibrated null; W_c has an unbiased linear estimator)",
           tnb[100] > tnb[1000] > tnb[10000] > 0)
B4["trace_norm_bias_product"] = tnb

RES["meta"]["runtime_s"] = round(time.perf_counter() - T_START, 1)
RES["summary"] = {"passed": sum(results), "total": len(results)}
OUT.parent.mkdir(exist_ok=True)


def fl(o):
    if isinstance(o, dict):
        return {str(k): fl(v) for k, v in o.items()}
    if isinstance(o, (list, tuple)):
        return [fl(v) for v in o]
    if isinstance(o, (np.floating, np.integer)):
        return o.item()
    return o


OUT.write_text(json.dumps(fl(RES), indent=1) + "\n")
print(f"\n{sum(results)} of {len(results)} checks passed ({RES['meta']['runtime_s']} s)")
sys.exit(0 if all(results) else 1)
