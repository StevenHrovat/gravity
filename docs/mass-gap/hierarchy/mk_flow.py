"""The layer-by-layer zoom-out of a lattice gauge theory in the Migdal-Kadanoff approximation, for U(1) and SU(2), in d = 3 and d = 4.

Why this is here (docs/mass-gap/README.md, "The bridge"): a proof of the mass gap has to carry control from short distances (where the
coupling is weak, the part the 2026 existence proof handles) out to long distances (where the coupling is strong and a gap is already a
theorem on the lattice). The Migdal-Kadanoff recursion is the zoom-out made exactly computable by pretending the lattice is a tree of
layers, the shape closest to DMP's depth-ordered grant graph. Tomboulis (arXiv:0707.2179) tried to turn exactly these decimations into a
proof of confinement for all couplings; Ito and Seiler (arXiv:0711.4930, 0803.3019) found unproven steps and noted that the argument
"would seem to work" for U(1) too, although U(1) in four dimensions is known to have a massless photon (Guth 1980; Froehlich and Spencer
1982). This script measures how the recursion treats the two groups.

The recursion (b = 2): a plaquette weight f (a class function on the group) becomes
  1. bond moving:  f -> f^(b^(d-2))   (pointwise power; d = 4: f^4, d = 3: f^2)
  2. decimation:   c_r -> c_r^(b^2)    (normalised character coefficients; c_r^4)
Everything is done in character space with positive coefficients only (no cancellation), in mpmath at 60 digits, because for U(1) the
flow at weak coupling is exponentially small and invisible in double precision.

Effective coupling. The first step mostly reshapes a Wilson weight into the heat-kernel (Villain) shape that the recursion keeps, and
that reshaping alone moves a Wilson-matched beta by about +1/2 at weak coupling (for U(1) exactly 1/2: I_1/I_0 = 1 - 1/(2b) - 1/(8b^2)
against e^(-1/(2b)) = 1 - 1/(2b) + 1/(8b^2)). The flow is therefore read in the heat-kernel coordinate, which the decimation divides by
b^2 exactly: SU(2) beta_hk = -3 / (2 ln c_2), U(1) beta_V = -1 / (2 ln c_1); both equal the Wilson beta to leading order at weak
coupling. The Wilson-matched beta is reported too.
"""

import json
import sys

import mpmath as mp

mp.mp.dps = 60
N = 220  # characters kept: SU(2) n = 1..N (n = 2j + 1, the dimension); U(1) n = 0..N


# ------------------------------------------------------------------------------------------------------------- SU(2) in character space


def su2_wilson(beta):
    """e^(beta cos t) = (2/beta) sum_n n I_n(beta) chi_n(t): coefficients a_n of chi_n, n = 1..N (index 0 unused)."""
    return [mp.mpf(0)] + [n * mp.besseli(n, beta) for n in range(1, N + 1)]


def su2_product(a, b):
    """(sum a_m chi_m)(sum b_n chi_n) = sum_k c_k chi_k with chi_m chi_n = sum_{k=|m-n|+1, step 2}^{m+n-1} chi_k (Clebsch-Gordan)."""
    # prefix sums of b over each parity class
    pre = {0: [mp.mpf(0)] * (N + 2), 1: [mp.mpf(0)] * (N + 2)}
    for par in (0, 1):
        s = mp.mpf(0)
        for n in range(0, N + 1):
            if n >= 1 and n % 2 == par:
                s += b[n]
            pre[par][n] = s

    def bsum(lo, hi, par):  # sum of b_n for lo <= n <= hi, n of parity par, within 1..N
        hi = min(hi, N)
        if hi < lo:
            return mp.mpf(0)
        return pre[par][hi] - (pre[par][lo - 1] if lo >= 1 else 0)

    c = [mp.mpf(0)] * (N + 1)
    for k in range(1, N + 1):
        s = mp.mpf(0)
        for m in range(1, N + 1):
            if a[m] == 0:
                continue
            lo, hi = abs(k - m) + 1, k + m - 1
            if lo > N:
                continue
            s += a[m] * bsum(lo, hi, (k + m + 1) % 2)
        c[k] = s
    return c


def su2_coeffs(a):
    """Normalised coefficients c_n = a_n / (n a_1)."""
    return [None] + [a[n] / (n * a[1]) for n in range(1, N + 1)]


def su2_from_coeffs(c):
    return [mp.mpf(0)] + [n * c[n] for n in range(1, N + 1)]


def su2_beta_eff(c2):
    return mp.findroot(lambda x: mp.besseli(2, x) / mp.besseli(1, x) - c2, (mp.mpf("0.01"), mp.mpf(400)), solver="anderson")


# -------------------------------------------------------------------------------------------------------------- U(1) in character space


def u1_wilson(beta):
    """e^(beta cos t) = sum_n I_n(beta) e^(i n t): a_n for n = 0..N (a_-n = a_n)."""
    return [mp.besseli(n, beta) for n in range(0, N + 1)]


def u1_product(a, b):
    def get(x, n):
        n = abs(n)
        return x[n] if n <= N else mp.mpf(0)

    c = [mp.mpf(0)] * (N + 1)
    for k in range(0, N + 1):
        s = mp.mpf(0)
        for n in range(-N, N + 1):
            if abs(k - n) <= N:
                s += get(a, n) * get(b, k - n)
        c[k] = s
    return c


def u1_coeffs(a):
    return [a[n] / a[0] for n in range(0, N + 1)]


def u1_from_coeffs(c):
    return list(c)


def u1_beta_eff(c1):
    return mp.findroot(lambda x: mp.besseli(1, x) / mp.besseli(0, x) - c1, (mp.mpf("0.01"), mp.mpf(400)), solver="anderson")


# ------------------------------------------------------------------------------------------------------------------------- the step

GROUPS = {
    "SU(2)": dict(wilson=su2_wilson, product=su2_product, coeffs=su2_coeffs, from_coeffs=su2_from_coeffs, beta_eff=su2_beta_eff, fund=2),
    "U(1)": dict(wilson=u1_wilson, product=u1_product, coeffs=u1_coeffs, from_coeffs=u1_from_coeffs, beta_eff=u1_beta_eff, fund=1),
}


def power(G, a, p):
    out = a
    for _ in range(p - 1):
        out = G["product"](out, a)
    return out


def mk_step(G, a, d, b=2):
    a = power(G, a, b ** (d - 2))  # bond moving
    c = G["coeffs"](a)
    c = [None if x is None else x ** (b * b) for x in c]  # decimation
    return G["from_coeffs"](c)


def beta_of(G, a):
    return G["beta_eff"](G["coeffs"](a)[G["fund"]])


def beta_hk(group, a):
    """The heat-kernel (Villain) coordinate of a weight: decimation divides it by b^2 exactly."""
    G = GROUPS[group]
    c = G["coeffs"](a)[G["fund"]]
    k = 3 if group == "SU(2)" else 1
    return -mp.mpf(k) / (2 * mp.log(c))


def trajectory(group, d, beta0, steps, stop=0.3):
    """Start from the Wilson weight at beta0 and zoom out step by step. Each row: step, beta_hk, the Wilson-matched beta, and the
    drop of beta_hk over the step (positive: towards strong coupling)."""
    G = GROUPS[group]
    a = G["wilson"](mp.mpf(str(beta0)))
    prev = beta_hk(group, a)
    rows = [{"step": 0, "beta_hk": float(prev), "beta_wilson": float(beta0), "drop": None}]
    for s in range(1, steps + 1):
        a = mk_step(G, a, d)
        bh = beta_hk(group, a)
        rows.append({"step": s, "beta_hk": float(bh), "beta_wilson": float(beta_of(G, a)), "drop": mp.nstr(prev - bh, 6)})
        prev = bh
        if bh < stop:
            break
    return rows


if __name__ == "__main__":
    group, d, steps = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    betas = [float(x) for x in sys.argv[4].split(",")]
    res = {f"{group} d={d}": {str(b): trajectory(group, d, b, steps) for b in betas}}
    print(json.dumps(res, indent=1))
