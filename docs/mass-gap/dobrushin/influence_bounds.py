"""Single-link Dobrushin influence for Wilson lattice gauge theory: three bounds, for lgt's framework (step 4 of the mass-gap work).

Standard normalisation (as in single_link.py): SU(2) weight exp(beta * sum_p 1/2 Re tr U_p), U(1) weight exp(beta * sum_p cos theta_p).
lgt (mrdouglasny/lgt) uses exp(-beta_lgt * sum_p (n - Re tr U_p)) for U(n): beta = beta_lgt for U(1), beta = 2 beta_lgt for SU(2) in U(2).

A link sits in 2(d-1) plaquettes; changing one neighbouring link swaps one staple v -> v'; the other 2(d-1)-1 staples sum to W.

1. lgt's bound (DobrushinVerification.lean): C <= 1 - exp(-4 n beta_lgt), counted over 8(d-1) neighbours.
2. The ratio (tanh) bound: if the density ratio of two probability measures stays within a factor R, their total variation is at most
   (sqrt R - 1)/(sqrt R + 1) = tanh(ln R / 4) (extremal two-level density; proof in README). Here ln R = 2 beta |v - v'| <= 4 beta,
   so C <= tanh(beta) (= tanh(n beta_lgt) in lgt's units). Rigorous and elementary.
3. The exact influence: numerically the supremum sits at W = 0, v' = -v (checked below for every d and beta in the table), where it
   has a closed form: C = L0(beta)/I0(beta) for U(1) and L1(beta)/I1(beta) for SU(2) (L = modified Struve function). Floating point.

The number of neighbours is 6(d-1) exactly (3 other links in each of the 2(d-1) plaquettes, no link shared twice); lgt's 8(d-1) is an
upper bound (it also counts the link itself once per plaquette).

Usage: python influence_bounds.py
"""

import json
import os

import numpy as np
from scipy import optimize, special

import single_link as S


def exact_closed(group, beta):
    return special.modstruve(0, beta) / special.i0(beta) if group == "U(1)" else special.modstruve(1, beta) / special.i1(beta)


def sup_check(group, beta, wmax):
    """Numerical supremum over the staple geometry with |W| <= wmax, against the closed form."""
    S.WMAX = wmax
    c, arg = S.sup_influence(group, beta)
    return c, exact_closed(group, beta)


def threshold(f, nb):
    return optimize.brentq(lambda b: nb * f(b) - 1.0, 1e-6, 5.0)


def main():
    out = {"rows": [], "sup_checks": []}
    print("Supremum check (numerical sup over W, v, v' against the closed form at W = 0, v' = -v):")
    for group in ("U(1)", "SU(2)"):
        for d in (2, 3, 4):
            wmax = 2 * (d - 1) - 1
            for beta in (0.05, 0.2, 0.5, 1.0):
                c, cf = sup_check(group, beta, wmax)
                out["sup_checks"].append({"group": group, "d": d, "beta": beta, "numerical_sup": c, "closed_form": cf})
                print(f"  {group:5s} d={d} beta={beta:4.2f}: sup {c:.6f}  closed form {cf:.6f}  ratio {c / cf:.5f}")
    print("\nThresholds in the standard beta (and in lgt's beta), d = 2, 3, 4:")
    for group in ("U(1)", "SU(2)"):
        to_lgt = 1.0 if group == "U(1)" else 0.5
        n = 1 if group == "U(1)" else 2
        for d in (2, 3, 4):
            nb_lgt, nb = 8 * (d - 1), 6 * (d - 1)
            lgt = threshold(lambda b: 1 - np.exp(-4 * n * b * to_lgt), nb_lgt)
            tanh_lgtcount = threshold(np.tanh, nb_lgt)
            tanh_exact = threshold(np.tanh, nb)
            exact = threshold(lambda b: exact_closed(group, b), nb)
            row = {"group": group, "d": d, "lgt": lgt, "tanh_lgt_count": tanh_lgtcount, "tanh_exact_count": tanh_exact, "exact": exact}
            out["rows"].append(row)
            print(f"  {group:5s} d={d}: lgt {lgt:.4f} ({lgt * to_lgt:.4f})   tanh, 8(d-1) {tanh_lgtcount:.4f} (x{tanh_lgtcount / lgt:.2f})"
                  f"   tanh, 6(d-1) {tanh_exact:.4f} (x{tanh_exact / lgt:.2f})   exact {exact:.4f} (x{exact / lgt:.2f})")
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "influence_bounds.json"), "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
