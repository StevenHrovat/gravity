"""Re-derive the numbers quoted in mass-gap.tex from standard inputs (A) and from the stored results (F).

    python checks.py        (run from docs/mass-gap/paper/; needs numpy and scipy)

Each check prints PASS or FAIL with the value it found; the exit code is the number of failures.
"""
import json
import math
import os
import sys

import numpy as np
from scipy import special, stats

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, "..", "results")
DOB = os.path.join(HERE, "..", "dobrushin")
fails = 0


def check(name, value, target, tol):
    global fails
    ok = abs(value - target) <= tol
    fails += not ok
    print(f"{'PASS' if ok else 'FAIL'}  {name}: {value:.6g} (paper {target}, tolerance {tol})")


def load(*p):
    return json.load(open(os.path.join(*p)))


# ---------------------------------------------------------------- A: analytic
# A1 Migdal-Kadanoff closed form N^2 (1 - 1/b^2) / 12 at weak coupling
check("A1 MK closed form, SU(2), b = 2", 4 * (1 - 1 / 4) / 12, 0.25, 1e-12)
check("A2 MK closed form, SU(3), b = 2", 9 * (1 - 1 / 4) / 12, 0.5625, 1e-12)
b0 = 11 * 2 / (48 * math.pi ** 2)
check("A3 one-loop drop per halving, SU(2): 8 b0 ln 2", 8 * b0 * math.log(2), 0.2575, 5e-5)
tree3, loop3 = 4 * (1 - 1 / 9) / 12, 8 * b0 * math.log(3)
check("A4 tree off at b = 3 (fraction)", abs(tree3 - loop3) / loop3, 0.27, 0.01)
# A5 area-law window for d = 4: e^{2 beta} - 1 <= 1 / (4 e^{65} 65^4)
d = 4
eps = 1 / (4 * math.exp(16 * d + 1) * (16 * d + 1) ** 4)
check("A5 area-law beta window, d = 4 (x 1e-37)", math.log1p(eps) / 2 / 1e-37, 4.0, 0.3)
check("A6 area-law base below 1 at the edge", math.exp(16 * d + 1) * eps, 0.0, 1 - 1e-9)
# A7 the TV lemma: two-valued densities attain tanh(ln R / 4); random densities never exceed it
rng = np.random.default_rng(1)
worst = 0.0
for _ in range(2000):
    R = math.exp(rng.uniform(0.01, 4))
    g = np.exp(rng.uniform(0, math.log(R), size=rng.integers(2, 6)))
    w = rng.dirichlet(np.ones(len(g)))
    g = g / np.dot(w, g)                      # density with mean 1 under weights w
    if g.max() / g.min() > R * (1 + 1e-12):
        continue
    worst = max(worst, np.dot(w, np.clip(g - 1, 0, None)) / math.tanh(math.log(R) / 4))
check("A7 TV lemma: excess of TV / tanh(ln R/4) over 1, random densities (0 = never exceeded)", max(worst - 1, 0.0), 0, 1e-9)
m = 1 / math.sqrt(math.e ** 2)
check("A8 TV lemma attained (R = e^2, m = 1/sqrt R)", (math.e ** 2 * m - 1) * (1 - m) / (math.e ** 2 * m - m), math.tanh(0.5), 1e-12)
# A9 Struve/Bessel small-beta slopes
bt = 1e-4
check("A9 U(1): L0/I0 slope 2/pi", special.modstruve(0, bt) / special.iv(0, bt) / bt, 2 / math.pi, 1e-6)
check("A10 SU(2): L1/I1 slope 4/(3 pi)", special.modstruve(1, bt) / special.iv(1, bt) / bt, 4 / (3 * math.pi), 1e-6)

# ---------------------------------------------------------------- F: stored results
ttl = load(RES, "ttl_summary.json")
quoted = {2.3: (0.350, 1.20, 0.83, 0.291), 2.4: (0.258, 1.01, 0.99, 0.256), 2.5: (0.182, 0.720, 1.39, 0.253),
          2.6: (0.140, 0.52, 1.92, 0.268), 2.7: (0.106, 0.39, 2.54, 0.268)}
for p in ttl:
    q = quoted[round(p["beta"], 2)]
    for name, key, val in zip(("a sqrt(sigma)", "a m", "TTL ticks", "TTL sqrt(sigma)"),
                              ("a_sqrt_sigma", "a_m_0pp", "ttl_ticks", "ttl_sqrt_sigma"), q):
        check(f"F1 TTL table beta {p['beta']} {name}", p[key][0], val, 0.0051 if val < 1 else 0.051)
y = np.array([p["ttl_sqrt_sigma"][0] for p in ttl])
ye = np.array([p["ttl_sqrt_sigma"][1] for p in ttl])
w = 1 / ye ** 2
c0 = np.sum(w * y) / np.sum(w)
chi2 = np.sum(w * (y - c0) ** 2)
check("F2 constant fit value", c0, 0.2603, 0.00005)
check("F3 constant fit p", stats.chi2.sf(chi2, len(y) - 1), 0.014, 0.0005)
check("F4 beta 2.3 errors above the constant", (y[0] - c0) / ye[0], 3.0, 0.05)
ex = load(RES, "ttl_extrapolation.json")
check("F5 extrapolation c", ex["c"][0], 0.2470, 0.00005)
check("F6 extrapolation k", ex["k"][0], 0.30, 0.005)
check("F7 extrapolation p", ex["p"], 0.15, 0.005)
check("F8 c against 1/3.74 (errors)", abs(ex["c"][0] - 1 / 3.74) / math.hypot(ex["c"][1], 0.009), 1.9, 0.05)
t23, t27 = ttl[0], ttl[-1]
check("F9 TTL tick growth 2.3 -> 2.7", t27["ttl_ticks"][0] / t23["ttl_ticks"][0], 3.05, 0.005)
check("F10 a sqrt(sigma) ratio 2.3 / 2.7", t23["a_sqrt_sigma"][0] / t27["a_sqrt_sigma"][0], 3.31, 0.005)

ph = load(RES, "u1_photon_test.json")["coulomb"]
for b, q in zip(ph["boxes"], (6.01, 6.26, 6.24)):
    check(f"F11 photon E1 * L at L = {b['L']}", b["E1"][0] * b["L"], q, 0.005)
b12 = ph["boxes"][1]
check("F12 L = 12 errors above massless", (b12["E1"][0] - b12["E_free"]) / b12["E1"][1], 2.03, 0.005)
check("F13 photon m^2", ph["m2"][0], 0.0044, 0.00005)

lat = {(round(x["beta"], 2), x["L"]): x for x in load(RES, "lattice_summary.json")}
check("F14 beta 2.4 a sqrt(sigma)", lat[(2.4, 14)]["a_sqrt_sigma"][0], 0.273, 0.0005)
check("F15 beta 2.4 a m", lat[(2.4, 14)]["a_m_0pp"][0], 0.99, 0.005)
x = lat[(2.5, 16)]["a_sqrt_sigma"]
check("F16 beta 2.5 a sqrt(sigma) errors from Teper 0.1834(26)", (x[0] - 0.1834) / math.hypot(x[1], 0.0026), 3.9, 0.05)

vx = {round(r["beta"], 2): r for r in load(RES, "vortex_summary.json")}
v = vx[2.3]
check("F17 vortex 2.3: proj/full R = 3", v["R"]["3"]["proj_over_full"][0], 0.68, 0.005)
check("F18 vortex 2.3: removed/full R = 3", v["R"]["3"]["removed_over_full"][0], 0.34, 0.005)
check("F19 vortex 2.3: proj/full R = 4", v["R"]["4"]["proj_over_full"][0], 0.81, 0.005)
check("F20 vortex 2.3: removed/full R = 4", v["R"]["4"]["removed_over_full"][0], 0.07, 0.005)
check("F21 vortex 2.3: chi_full R = 3, 4", v["R"]["3"]["chi_full"][0] + v["R"]["4"]["chi_full"][0], 0.214 + 0.184, 0.001)
check("F22 vortex 2.3: chi_proj R = 3, 4", v["R"]["3"]["chi_proj"][0] + v["R"]["4"]["chi_proj"][0], 0.145 + 0.149, 0.001)
check("F23 vortex 2.3 follow-up: proj/sigma R = 4", v["followup"]["R"]["4"]["proj_over_sigma"][0], 1.21, 0.005)
check("F24 vortex 2.3 follow-up: proj/sigma R = 5", v["followup"]["R"]["5"]["proj_over_sigma"][0], 1.18, 0.005)

ib = {(r["group"], r["d"]): r for r in load(DOB, "influence_bounds.json")["rows"]}
check("F25 exact influence over lgt, U(1), d = 4", ib[("U(1)", 4)]["exact"] / ib[("U(1)", 4)]["lgt"], 8, 0.5)
check("F26 exact influence over lgt, SU(2), d = 4", ib[("SU(2)", 4)]["exact"] / ib[("SU(2)", 4)]["lgt"], 12, 0.5)

print(f"\n{fails} failure(s)")
sys.exit(fails)
