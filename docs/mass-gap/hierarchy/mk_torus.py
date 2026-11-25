"""Migdal-Kadanoff zoom-out for SU(2) and SU(3) on the eigenvalue torus (double precision; for the rates, not for U(1)'s tiny tail).

Same recursion as mk_flow.py (b = 2, d = 4): bond moving f -> f^4 pointwise, decimation c_r -> c_r^4 on the normalised character
coefficients c_r = a_r / (d_r a_0). Here a class function lives on a grid of the maximal torus; coefficients come from Weyl's
integration formula, int f conj(chi_r) dHaar ~ sum f * conj(num_r) * Delta (chi_r = num_r / Delta, Weyl's character formula), so no
division is needed there; the weight is rebuilt as sum d_r c_r chi_r on a grid offset from the walls where Delta = 0.

Effective coupling: the heat-kernel coordinate beta_hk = -N C2(fund) / ln c_fund (SU(2): -3 / (2 ln c), SU(3): -4 / ln c), equal to the
Wilson beta = 2N/g^2 at weak coupling; the decimation divides the heat-kernel time by 4 exactly.

Usage: python mk_torus.py GROUP STEPS BETA[,BETA...] [M] [P]    (GROUP SU2 or SU3; M grid points per angle; P irrep cutoff)
"""

import json
import sys

import numpy as np


def su2_setup(M, P):
    th = (np.arange(M) + 0.37) * 2 * np.pi / M
    z = np.exp(1j * th)
    delta = z - 1 / z                                    # Weyl denominator (up to a constant)
    irreps = [(n,) for n in range(1, P + 1)]             # n = dimension = 2j + 1
    num = {r: z ** r[0] - z ** (-r[0]) for r in irreps}
    dim = {r: r[0] for r in irreps}
    c2 = {r: (r[0] ** 2 - 1) / 4 for r in irreps}
    retr = 2 * np.cos(th)
    return dict(N=2, delta=delta, irreps=irreps, num=num, dim=dim, c2=c2, retr=retr, fund=(2,), triv=(1,))


def su3_setup(M, P):
    a = (np.arange(M) + 1 / 3) * 2 * np.pi / M
    b = (np.arange(M) + 0.71) * 2 * np.pi / M
    t1, t2 = np.meshgrid(a, b, indexing="ij")
    z1, z2 = np.exp(1j * t1), np.exp(1j * t2)
    z3 = 1 / (z1 * z2)
    zs = (z1, z2, z3)

    def det_pow(l):
        m = [[zs[k] ** l[j] for k in range(3)] for j in range(3)]
        return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1]) - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
                + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))

    delta = det_pow((2, 1, 0))
    irreps = [(p, q) for p in range(P + 1) for q in range(P + 1 - p)]
    num = {}
    for (p, q) in irreps:
        num[(p, q)] = det_pow((p + q + 2, q + 1, 0))
    dim = {(p, q): (p + 1) * (q + 1) * (p + q + 2) // 2 for (p, q) in irreps}
    c2 = {(p, q): (p * p + q * q + p * q + 3 * p + 3 * q) / 3 for (p, q) in irreps}
    retr = np.real(z1 + z2 + z3)
    return dict(N=3, delta=delta, irreps=irreps, num=num, dim=dim, c2=c2, retr=retr, fund=(1, 0), triv=(0, 0))


def coeffs(G, f):
    w = f * G["delta"]
    a = {r: np.real(np.sum(w * np.conj(G["num"][r]))) for r in G["irreps"]}
    return {r: a[r] / (G["dim"][r] * a[G["triv"]]) for r in G["irreps"]}


def rebuild(G, c):
    s = np.zeros_like(G["delta"])
    for r in G["irreps"]:
        s = s + G["dim"][r] * c[r] * G["num"][r]
    f = np.real(s / G["delta"])
    return f / np.max(f)


def beta_hk(G, c):
    return -G["N"] * G["c2"][G["fund"]] / np.log(c[G["fund"]])


def trajectory(G, beta0, steps):
    f = np.exp((beta0 / G["N"]) * (G["retr"] - G["N"]))  # Wilson weight exp((beta/N) Re tr U), scaled
    c = coeffs(G, f)
    prev = beta_hk(G, c)
    rows = [{"step": 0, "beta_hk": float(prev), "drop": None}]
    for s in range(1, steps + 1):
        f = rebuild(G, c) ** 4                  # bond moving (d = 4)
        c = coeffs(G, f)
        c = {r: v ** 4 for r, v in c.items()}   # decimation
        bh = beta_hk(G, c)
        rows.append({"step": s, "beta_hk": float(bh), "drop": float(prev - bh)})
        prev = bh
        if bh < 0.5:
            break
    return rows


if __name__ == "__main__":
    group, steps = sys.argv[1], int(sys.argv[2])
    betas = [float(x) for x in sys.argv[3].split(",")]
    M = int(sys.argv[4]) if len(sys.argv) > 4 else (512 if group == "SU2" else 160)
    P = int(sys.argv[5]) if len(sys.argv) > 5 else (120 if group == "SU2" else 44)
    G = su2_setup(M, P) if group == "SU2" else su3_setup(M, P)
    print(json.dumps({f"{group} d=4 M={M} P={P}": {str(b): trajectory(G, b, steps) for b in betas}}, indent=1))
