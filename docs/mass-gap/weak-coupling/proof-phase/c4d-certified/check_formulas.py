"""Float checks of the closed forms used by cert_measured.py (PREREG.md, Checks): x(r) = E cos t, q(r) = E cos^2 t, Z(r), zeta, V,
||g||^2, ||g_1||^2 against Gauss-Legendre quadrature on S^3 in coordinates u = cos t A^ + sin t w, w in S^2 (measure (2/pi) sin^2 t dt dy/2,
y = w.e). Plus: the bound at r = 0 and the Bessel-ratio form."""
import os
os.environ["CUDA_VISIBLE_DEVICES"] = "-1"
import numpy as np
from numpy.polynomial.legendre import leggauss
from math import factorial, sqrt, pi

def S(nu, y, K=60):
    return sum(y**k / (factorial(k) * factorial(k + nu)) for k in range(K))

def T(y): return S(2, y) / S(1, y)
def xf(r): return r / 2 * T(r * r / 4)
def qf(r): return 1 - 1.5 * T(r * r / 4)
def Zf(r): return S(1, r * r / 4)

tg, tw = leggauss(400); tg = (tg + 1) * pi / 2; tw = tw * pi / 2
yg, yw = leggauss(60)
Tt, Yy = np.meshgrid(tg, yg, indexing="ij")
W = np.outer(tw, yw) * (2 / pi) * np.sin(Tt) ** 2 / 2

def E(fun, r):
    rho = np.exp(r * np.cos(Tt)); Z = (W * rho).sum()
    return (W * rho * fun).sum() / Z

worst = 0.0
rng = np.random.default_rng(1)
for r in [0.0, 0.3, 0.8, 1.2, 2.0] + list(rng.uniform(0, 1.2, 3)):
    cT, sT = np.cos(Tt), np.sin(Tt)
    # checks of moments
    d1 = abs(E(cT, r) - xf(r)); d2 = abs(E(cT ** 2, r) - qf(r))
    Z = (W * np.exp(r * cT)).sum(); d3 = abs(Z - Zf(r))
    zeta = (W * np.exp(2 * r * cT)).sum() / Z ** 2
    d4 = abs(zeta - Zf(2 * r) / Zf(r) ** 2) / zeta
    for c2 in (0.0, 0.3, 1.0):
        c = sqrt(c2); s = sqrt(1 - c2)
        f = c * cT + s * sT * Yy
        m = E(f, r)
        rho = np.exp(r * cT) / Z
        g = (f - m) * rho
        norm2 = (W * g * g).sum()
        V = c2 * (qf(2 * r) - 2 * xf(r) * xf(2 * r) + xf(r) ** 2) + (1 - c2) * (1 - qf(2 * r)) / 3
        d5 = abs(norm2 - zeta * V)
        g1 = 4 * ((W * g * cT).sum() ** 2 + (W * g * sT * Yy).sum() ** 2)
        g1f = 4 * (c2 * (qf(r) - xf(r) ** 2) ** 2 + (1 - c2) * ((1 - qf(r)) / 3) ** 2)
        d6 = abs(g1 - g1f)
        worst = max(worst, d1, d2, d3, d4, d5, d6)
    print(f"r={r:.3f}: |dx| {d1:.1e} |dq| {d2:.1e} |dZ| {d3:.1e} |dzeta|/zeta {d4:.1e}; last c2: |d||g||^2| {d5:.1e} |d||g1||^2| {d6:.1e}")
print("max deviation", worst)
# r = 0: bound sqrt(1/12), exact k_F = 8/(9 pi)
print("r=0: sqrt(g1^2/3 + (g^2-g1^2)/8) =", sqrt(0.25 / 3), " exact KR 8/(9pi) =", 8 / (9 * pi))
