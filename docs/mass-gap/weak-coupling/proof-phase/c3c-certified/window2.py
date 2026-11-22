"""PREREG run 3, second part: the certified two-parameter window (b_A, b_F) from the certified suprema in cert_window.json.

Per-plaquette W1 influence bound at (b_A, b_F), a = 6 |b_F| (NOTE.md 2.4):
  k = |b_F| NF + (8 |b_A| / 3) (NA + De + Do),
  NF = e^a sqrt(zeta) (sqrt(sigma2) + sinh a) / sqrt 3,  De = pi (cosh a - 1),
  Do = (pi / 2) sinh a sqrt((Vh + (cosh a - 1)^2) sigma1),
with NA = sup B1, zeta, sigma1, sigma2, Vh the certified suprema at |b_A| (both signs; the maximum is used). All terms increase
in |b_A| (nested configuration sets) and in |b_F|, so k at a corner bounds k on the rectangle below it. Evaluated in mpmath
(50 digits) and rounded UP to a rational with denominator 10^7; the corner list is written to window2.json and is what
formal/ProofPhase/Certified/AdjointW.lean states (cornerA, cornerF, cornerK).
"""
import json
import math
import os

import mpmath as mp

mp.mp.dps = 50
HERE = os.path.dirname(os.path.abspath(__file__))
W = json.load(open(os.path.join(HERE, "cert_window.json")))


def sups(bA):
    """maximum over the two signs of certified suprema valid at |b_A| = bA: any certified entry of the same sign with
    |b_A'| >= bA is valid (monotone in |b_A|); the smallest such value is taken for each quantity separately."""
    if bA == 0:
        return dict(B1=mp.mpf(1) / 16, zeta=mp.mpf(1), sigma1=mp.mpf(1) / 4, sigma2=mp.mpf(1) / 4, Vh=mp.mpf(1) / 24)
    out = None
    for pos in (True, False):
        cands = [v for v in W.values() if v.get("certified") and abs(v["b_A"]) >= bA - 1e-12 and (v["b_A"] > 0) == pos]
        if not cands:
            return None
        vals = {k: mp.mpf(min(c[k + "_sup"] for c in cands)) for k in ("B1", "zeta", "sigma1", "sigma2", "Vh")}
        out = vals if out is None else {k: max(out[k], vals[k]) for k in vals}
    return out


def kbound(bA, bF, s):
    a = 6 * mp.mpf(bF)
    NF = mp.e ** a * mp.sqrt(s["zeta"]) * (mp.sqrt(s["sigma2"]) + mp.sinh(a)) / mp.sqrt(3)
    De = mp.pi * (mp.cosh(a) - 1)
    Do = mp.pi / 2 * mp.sinh(a) * mp.sqrt((s["Vh"] + (mp.cosh(a) - 1) ** 2) * s["sigma1"])
    return mp.mpf(bF) * NF + 8 * mp.mpf(bA) / 3 * (s["B1"] + De + Do)


corners = []
for bA in (0.21, 0.2, 0.15, 0.1, 0.05, 0.0):
    s = sups(bA)
    if s is None:
        print(f"|b_A| = {bA}: no certified suprema for both signs yet")
        continue
    bF = 0.0
    step = 0.0005
    while 18 * kbound(bA, bF + step, s) < 1:
        bF += step
    k = kbound(bA, bF, s)
    kq = math.ceil(k * 10 ** 7) / 10 ** 7
    corners.append(dict(bA=bA, bF=round(bF, 4), k=float(k), k_rounded_up=f"{int(round(kq * 1e7))}/10000000",
                        column=float(18 * mp.mpf(kq))))
    print(f"|b_A| <= {bA:.3f}, |b_F| <= {bF:.4f}: k <= {float(k):.6f} (rounded up {kq:.7f}), column 18 k = {18 * kq:.7f}"
          f";  NA {float(s['B1']):.5f} zeta {float(s['zeta']):.4f} sigma2 {float(s['sigma2']):.4f}")
json.dump(corners, open(os.path.join(HERE, "window2.json"), "w"), indent=1)
