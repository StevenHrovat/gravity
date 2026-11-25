"""Criterion constants and coupling matching for attempts/r2-curvature (see PREREG.md). CPU only, seconds.

S^3 = SU(2), Haar. For functions of two coordinates (x1, x2) of u in S^3 the pushforward of Haar is uniform on the unit disk
(Archimedes), so E[F(x1, x2)] = (1/pi) * integral over the disk. Zonal laws reduce to the angle theta with density ~ sin^2.
"""
import json
import os

os.environ["CUDA_VISIBLE_DEVICES"] = "-1"
import numpy as np
from scipy import integrate, optimize, special

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "criterion_numbers.json")


def disk_mean(F, w=None):
    """E[F] under (w * uniform on the disk), normalised; F, w functions of (x1, x2). Polar Gauss-Legendre."""
    nr, nt = 400, 800
    r, wr = np.polynomial.legendre.leggauss(nr)
    r = 0.5 * (r + 1.0); wr = 0.5 * wr
    t = np.linspace(0, 2 * np.pi, nt, endpoint=False); wt = np.full(nt, 2 * np.pi / nt)
    R, T = np.meshgrid(r, t, indexing="ij")
    W = np.outer(wr, wt) * R
    x1, x2 = R * np.cos(T), R * np.sin(T)
    ww = W if w is None else W * w(x1, x2)
    return float(np.sum(ww * F(x1, x2)) / np.sum(ww))


res = {}

# N1: h1 = x2 (dipole)
lo1 = disk_mean(lambda x1, x2: np.arcsin(x2) * x2)
res["N1"] = {"lower_arcsin": lo1, "exact_8_over_9pi": 8 / (9 * np.pi), "upper_Hm1": 1 / (2 * np.sqrt(3))}

# N2: h2 = x1 x2 (quadrupole)
h2sq = disk_mean(lambda x1, x2: (x1 * x2) ** 2)


def f_arc(x1, x2):
    y1, y2 = (x1 + x2) / np.sqrt(2), (x1 - x2) / np.sqrt(2)
    return 0.5 * (np.arcsin(np.abs(y1)) - np.arcsin(np.abs(y2)))


lo2_arc = disk_mean(lambda x1, x2: f_arc(x1, x2) * x1 * x2)
# a one-parameter family interpolating: f = (1/L) * [ (1-s) h2 + s f_arc ], Lipschitz <= 1 by convexity
lo2 = max(h2sq, lo2_arc)
res["N2"] = {"E_h2_sq_(test_h2)": h2sq, "lower_arcsin_test": lo2_arc, "lower_best": lo2, "upper_Hm1": np.sqrt(1 / 192)}

# N3: adjoint coefficient at the aligned configuration vs linearised
n3 = []
for bA in [0.1, 0.25, 0.5, 0.75, 1.0]:
    c = 4 * bA / 3
    w = lambda x1, x2, c=c: np.exp(6 * c * x1 ** 2)
    ex = disk_mean(lambda x1, x2: x1 ** 2, w); eb = disk_mean(lambda x1, x2: x2 ** 2, w)
    n3.append({"beta_A": bA, "aligned_lower": (ex - eb) / 6, "lin_lower": 2 * c * lo2, "lin_upper": 2 * c * np.sqrt(1 / 192)})
res["N3"] = n3

# N4: vMF(r n) on S^3, tangential (test arcsin x2) and radial (exact 1D transport in theta)
n4 = []
th = np.linspace(0, np.pi, 20001)
for r in [0.0, 0.25, 0.5, 1.0, 1.5, 2.0, 3.0]:
    w = lambda x1, x2, r=r: np.exp(r * x1)
    tang = disk_mean(lambda x1, x2: np.arcsin(x2) * x2, w)
    p = np.exp(r * np.cos(th)) * np.sin(th) ** 2; p /= integrate.trapezoid(p, th)
    m = integrate.trapezoid(np.cos(th) * p, th)
    F = integrate.cumulative_trapezoid((np.cos(th) - m) * p, th, initial=0)
    rad = integrate.trapezoid(np.abs(F), th)
    n4.append({"r": r, "tangential_lower": tang, "radial_exact": rad})
res["N4"] = n4

# N5: matching
def uF(b):
    return special.iv(2, b) / special.iv(1, b)


def uA(bA):
    f = lambda t: np.exp((bA / 3) * (4 * np.cos(t) ** 2 - 1)) * np.sin(t) ** 2
    g = lambda t: (4 * np.cos(t) ** 2 - 1) * f(t)
    return integrate.quad(g, 0, np.pi)[0] / integrate.quad(f, 0, np.pi)[0] / 3


def inv(fun, target, hi=50.0):
    return optimize.brentq(lambda b: fun(b) - target, 1e-60, hi, xtol=1e-300)


n5 = []
for L in [2, 2.5, 3, 3.5, 4, 5, 6, 8.4]:
    row = {"L1_sqrt_sigma": L, "beta_F_from_sigma": inv(uF, np.exp(-L * L))}
    for mr in [3.5, 3.75, 4.0]:
        u = np.exp(-mr * L / 4)
        row[f"m{mr}"] = {"u": u, "beta_A": inv(uA, u), "beta_Wilson_from_m": inv(uF, u)}
    n5.append(row)
res["N5"] = n5

# N6: thresholds and alpha
h1 = 8 / (9 * np.pi)
bF_star = 1 / (18 * h1)
bA_star_lo, bA_star_hi = 1 / (48 * np.sqrt(1 / 192)), 1 / (48 * lo2)
res["N6"] = {
    "beta_F_star_W1_linearised": bF_star, "alpha_F_star": 1 / (np.pi * bF_star), "16_over_pi2": 16 / np.pi ** 2,
    "beta_F_star_BE_SZZ": 1 / 12, "alpha_BE": 12 / np.pi,
    "beta_A_star_range": [bA_star_lo, bA_star_hi],
    "beta_eq_star_range": [8 / 3 * bA_star_lo, 8 / 3 * bA_star_hi],
    "alpha_eq_star_range": [1 / (np.pi * 8 / 3 * bA_star_hi), 1 / (np.pi * 8 / 3 * bA_star_lo)],
    "u_A_at_threshold": [uA(bA_star_lo), uA(bA_star_hi)],
    "u_F_at_threshold": uF(bF_star),
}
# entry scale L1*sqrt(sigma) = 4 ln(1/u*)/(m/sqrt(sigma))
ent = {}
for mr in [3.5, 3.75, 4.0]:
    ent[f"m{mr}"] = {
        "adjoint_lin_lo_hi": [4 * np.log(1 / uA(bA_star_lo)) / mr, 4 * np.log(1 / uA(bA_star_hi)) / mr],
        "wilson_fund": 4 * np.log(1 / uF(bF_star)) / mr,
        "wilson_fund_BE": 4 * np.log(1 / uF(1 / 12)) / mr,
    }
res["N6"]["entry_L1_sqrt_sigma"] = ent

json.dump(res, open(OUT, "w"), indent=1, default=float)
print(json.dumps(res, indent=1, default=float))
