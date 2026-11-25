#!/usr/bin/env python3
"""Diagnostics for grh_onebox_cert.py (NOT part of the proof): where does the margin go?

Reads the midpoint dump written by `grh_onebox_cert.py A N D auto c DUMP.json` and prints the smallest eigenvalues
(Arb's eigenvalue enclosure on the midpoint matrices) of
  G                     the Gram matrix of W on Poly_N (Rayleigh-Ritz: an upper bound for inf W/||f||^2),
  G - R/mu              coupling to degrees N..M-1 only,
  G - (R + T)/mu        plus the singular Legendre tail beyond M, pieces added exactly (not certified: cross terms),
  G - (R + 3T)/mu       the certified version (pieces combined by ||a+b+c||^2 <= 3 sum).
Usage: py grh_onebox_cert_diag.py DUMP.json
"""
import json
import sys

from flint import acb_mat, arb, arb_mat, ctx

ctx.prec = 300
d = json.load(open(sys.argv[1]))
N = len(d["G"])
mu = arb(d["mu"])
M = {k: arb_mat([[arb(x) for x in row] for row in d[k]]) for k in ("G", "R", "TL", "TR", "TJ")}
T = M["TL"] + M["TR"] + M["TJ"]


def lam(A, k=2):
    ev = sorted((e.real for e in acb_mat(A).eig(nonstop=True)), key=lambda v: float(v.mid()))
    return [v.str(5) for v in ev[:k]]


print(f"N = {N}, mu = {mu.str(8)}")
for name, A in (("G", M["G"]), ("G - R/mu", M["G"] - M["R"] * (1 / mu)),
                ("G - (R + T)/mu", M["G"] - (M["R"] + T) * (1 / mu)),
                ("G - (R + 3T)/mu", M["G"] - (M["R"] + T * 3) * (1 / mu))):
    print(f"  lambda_min({name:16s}) = {lam(A)}")
