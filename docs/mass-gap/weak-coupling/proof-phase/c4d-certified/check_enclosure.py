"""The interval enclosures of cert_measured.cell_values contain the values computed independently from mpmath's Bessel functions
(50 digits): x = I2/I1, q = 1 - 3 I2/(r I1), zeta = Z(2r)/Z(r)^2, Z = 2 I1/r."""
import os, sys, random
os.environ["CUDA_VISIBLE_DEVICES"] = "-1"
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cert_measured as cm
from mpmath import mp, besseli, mpf
mp.dps = 50
random.seed(3)
bad = 0; n = 0
for _ in range(300):
    r0 = random.uniform(0.0, 2.0)
    w = 0.0025
    r = cm.iv.mpf([cm.L(cm.Iv(r0).a), cm.U(cm.Iv(r0 + w).b)])
    x, q, x2, q2, zeta = cm.cell_values(r)
    for rr in (r0, r0 + w / 2, r0 + w):
        rr = mpf(rr)
        if rr == 0: continue
        Z = lambda t: 2 * besseli(1, t) / t
        ex = besseli(2, rr) / besseli(1, rr); eq = 1 - 3 * ex / rr
        ex2 = besseli(2, 2 * rr) / besseli(1, 2 * rr); eq2 = 1 - 3 * ex2 / (2 * rr)
        ez = Z(2 * rr) / Z(rr) ** 2
        for iv_, ev in ((x, ex), (q, eq), (x2, ex2), (q2, eq2), (zeta, ez)):
            n += 1
            if not (mpf(iv_.a) <= ev <= mpf(iv_.b)): bad += 1
print(f"{n} enclosure checks, {bad} failures")
