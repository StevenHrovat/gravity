"""PREREG run 4: CERTIFIED ceiling of the single-link W1 window (a rigorous LOWER bound on the supremum of N_A).

At a Klein-symmetric configuration (a, b eigenvectors of Q) the coefficient is exact (NOTE.md 2.2):
  N_A = E_rho[w(u_a, u_b)],  w(x, y) = |x y| min(arcsin|x|, arcsin|y|),
and (u_a, u_b) has density proportional to exp(a x^2 + b y^2) on the unit disk when the eigenvalues of Q on the plane
orthogonal to a, b are equal (the third and fourth coordinates then contribute a function of x^2 + y^2 only; constants dropped):
  * b_A > 0, configuration (s_a, s_b, s_3, s_4) = (3, 3, 0, 0): exponent 3 kappa (x^2 + y^2);
  * b_A < 0, configuration (1, 0, 2.5, 2.5) (five staples spread evenly in the orthogonal plane): exponent
    kappa x^2 + 2.5 kappa (1 - x^2 - y^2) = const + |kappa| (1.5 x^2 + 2.5 y^2).
In polar coordinates on the quadrant [0, pi/2] (the integrands are even in x and y): the weight is increasing in r and in theta
(b >= a); w is increasing in r, increasing in theta on [0, pi/4] and decreasing on [pi/4, pi/2]. Hence on every grid cell the
numerator integrand is >= (min of w) * (min of the weight) at known corners, and the denominator integrand <= its value at the
upper corner: a rigorous lower bound N_lo <= N_A. Floating point: libm exp/sin/cos/arcsin (errors of a few ulp) and sums of
positive terms; a relative margin of 1e-9 covers all rounding. If 48 |b_A| N_lo >= 1, the single-link W1 criterion fails at b_A
for this configuration, hence for the two-coupling action at b_A.

Usage: py cert_ceiling.py
"""
import json
import math
import os

os.environ.setdefault("CUDA_VISIBLE_DEVICES", "-1")
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


def bounds(a, b, n=3000):
    """(N_lo, N_float) for the density exp(a x^2 + b y^2) on the unit disk, 0 <= a <= b"""
    r = np.linspace(0, 1, n + 1)
    t = np.linspace(0, math.pi / 2, n + 1)
    rl, rh = r[:-1, None], r[1:, None]
    tl, th = t[None, :-1], t[None, 1:]
    area = (rh ** 2 - rl ** 2) / 2 * (math.pi / 2 / n)

    def wt(rr, tt):
        return np.exp(rr ** 2 * (a * np.cos(tt) ** 2 + b * np.sin(tt) ** 2))

    def w(rr, tt):
        x, y = rr * np.cos(tt), rr * np.sin(tt)
        return np.abs(x * y) * np.minimum(np.arcsin(np.minimum(x, 1)), np.arcsin(np.minimum(y, 1)))
    left = tl < math.pi / 4 - 1e-15
    wmin = np.where(left, w(rl, tl), w(rl, th))     # increasing in theta on [0, pi/4], decreasing after (grid has pi/4 as node)
    num_lo = np.sum(wmin * wt(rl, tl) * area) * (1 - 1e-9)
    den_hi = np.sum(wt(rh, th) * area) * (1 + 1e-9)
    rm, tm = (rl + rh) / 2, (tl + th) / 2
    nf = np.sum(w(rm, tm) * wt(rm, tm) * area) / np.sum(wt(rm, tm) * area)
    return num_lo / den_hi, nf


out = {}
for sign, conf in ((+1, "(3,3,0,0)"), (-1, "(1,0,2.5,2.5)")):
    # float scan for the crossing, then certify on the 0.005 grid above it
    def coeffs(bA):
        k = abs(4 * bA / 3)
        return (3 * k, 3 * k) if sign > 0 else (1.5 * k, 2.5 * k)
    bA = 0.2
    while True:
        lo, fl = bounds(*coeffs(bA), n=600)
        if 48 * bA * fl >= 1:
            break
        bA += 0.005
    while True:
        lo, fl = bounds(*coeffs(bA))
        col = 48 * bA * lo
        print(f"b_A = {sign * bA:+.3f}, configuration {conf}: N_A >= {lo:.6f} (float {fl:.6f}); column >= {col:.5f}",
              flush=True)
        if col >= 1:
            break
        bA += 0.005
    out[f"{sign * bA:+.3f}"] = dict(configuration=conf, N_lo=lo, N_float=fl, column_lo=col, fails=bool(col >= 1))
json.dump(out, open(os.path.join(HERE, "cert_ceiling.json"), "w"), indent=1)
