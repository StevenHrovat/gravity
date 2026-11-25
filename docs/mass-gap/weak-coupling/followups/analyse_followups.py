"""Reads sf_oneloop.json, u1_2d_lower.json, u1_2d_upper*.json and prints the numbers for the Result section of
PREREG-FOLLOWUPS.md. No computation beyond fits. Usage: py analyse_followups.py"""
import json
import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
TARGET = 8 * 11 * 2 / (48 * np.pi ** 2) * np.log(2)


def exp1():
    r = json.load(open(os.path.join(HERE, "sf_oneloop.json")))
    for g in ("SU2", "U1"):
        Ls = sorted(int(k.split("_")[1]) for k in r if k.startswith(g + "_"))
        ratio = {L: r["%s_%d" % (g, L)]["ratio"] for L in Ls}
        print("%s  beta_kappa - beta = Gamma1'/s_cl':" % g, " ".join("%d:%.5f" % (L, ratio[L]) for L in Ls))
        D = {L: ratio[2 * L] - ratio[L] for L in Ls if 2 * L in ratio}
        print("   Delta(L) (corrected definition beta_kappa = beta + Gamma1'/s_cl'):",
              " ".join("%d:%.5f" % (L, D[L]) for L in sorted(D)))
        fitL = [L for L in (4, 6, 8, 12, 16) if L in D]
        x = np.array([1 / L for L in fitL])
        y = np.array([D[L] for L in fitL])
        A = np.vstack([np.ones_like(x), x]).T
        (d0, d1), res, *_ = np.linalg.lstsq(A, y, rcond=None)
        print("   registered fit L in %s: Delta_inf = %.5f, d = %.4f, max residual %.5f" % (fitL, d0, d1,
              np.abs(A @ [d0, d1] - y).max()))
        fitL2 = [L for L in (8, 10, 12, 16) if L in D]
        x = np.array([1 / L for L in fitL2]); y = np.array([D[L] for L in fitL2])
        A = np.vstack([np.ones_like(x), x]).T
        (e0, e1), *_ = np.linalg.lstsq(A, y, rcond=None)
        print("   additional fit L in %s: Delta_inf = %.5f (not part of the verdict)" % (fitL2, e0))
        if g == "SU2":
            print("   target -%.4f; |Delta_inf + target| = %.4f; |Delta(16) + target| = %.4f" % (
                TARGET, abs(d0 + TARGET), abs(D[16] + TARGET)))
        else:
            print("   |Delta_inf| = %.4f; |Delta(16)| = %.4f" % (abs(d0), abs(D[16])))


def exp2():
    lo = json.load(open(os.path.join(HERE, "u1_2d_lower.json")))
    print("\nExperiment 2, lower bounds")
    for key in sorted(lo, key=float):
        e = lo[key]
        s = e["sigma"]
        rows = e["rows"]
        ge1 = [row["l"] for row in rows if row["gamma_lo"] >= 1]
        lstar = max(ge1) + 1 if ge1 else 2
        kmid = rows[-1]["kP"][rows[-1]["l"] // 2]
        k0 = rows[-1]["kP"][0]
        g = {row["l"]: row["gamma_lo"] for row in rows}
        print("beta=%s sigma=%.5f 1/sqrt(sigma)=%.3f  l*_lo=%d  l*_lo*sqrt(sigma)=%.3f  l*_lo*sigma=%.3f  "
              "k_lo(P) saturates: corner %.3f mid %.3f -> (kmid-1)*sqrt(sigma)=%.3f  kD=%.3f  gamma(2)=%.3f (Phi=0 %.3f)" % (
                  key, s, 1 / np.sqrt(s), lstar, lstar * np.sqrt(s), lstar * s, k0, kmid, (kmid - 1) * np.sqrt(s),
                  rows[-1]["kD"], g[2], rows[0]["gamma_lo_phi0"]))
        print("      gamma_lo:", " ".join("%d:%.3f" % (l, g[l]) for l in sorted(g) if l <= 12 or l % 4 == 0))


if __name__ == "__main__":
    exp1()
    exp2()
