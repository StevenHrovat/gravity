"""Exact free-photon act numbers on the lattice (no simulation; closed formulas). Cycle 5, workstream 5 (c5e-dmp).

Free lattice photon (Wilson/Villain quadratic action, Feynman gauge, any coupling), periodic box L^3 x infinite time, lattice units:
  one-photon energy at spatial momentum k:   sinh^2(E/2) = sum_i sin^2(k_i/2)        (pole of 1/(4 sin^2(w/2) + K^2) at w = iE)
  lowest one-photon state (k = 2 pi/L e_1):   E_1(L) = 2 asinh(sin(pi/L))            -> z_0^(1)(L) = L E_1(L) -> 2 pi
  lowest zero-momentum two-photon state:      E_2(L) = 2 E_1(L)                      -> z_0^(2)(L) = 2 z_0^(1)(L) -> 4 pi
  electric flux, cube (r4-conjw, proved):     E_e(L) = g^2 / (2 L)                   -> z_e = g^2 / 2 = 2 pi alpha, every L
The slice observables of the Lean definition (`VacObs`, all momenta) see z_0^(1); zero-momentum (A1++) operators see z_0^(2).
Doubling ratios z(2L)/z(L) are printed: the photon's own band for the doubling reading (it tends to 1, i.e. eta -> 1/2).
Check against existing data (lattice/README.md: U(1) beta = 1.2, 8^3 x 16: 0.70(3) and 1.33(9) at the two smallest momenta).
Usage: python photon_exact.py [out.json]
"""
import json
import math
import sys


def e1(L, n=1):
    return 2.0 * math.asinh(math.sin(math.pi * n / L))


def main():
    rows = []
    for L in (2, 3, 4, 6, 8, 10, 12, 14, 16, 20, 24, 28, 32, 48, 64):
        z1 = L * e1(L)
        rows.append({"L": L, "E1": e1(L), "z0_one_photon": z1, "z0_two_photon_zero_momentum": 2 * z1})
    by_L = {r["L"]: r for r in rows}
    doubling = []
    for L in (2, 3, 4, 6, 8, 10, 12, 14, 16, 24, 32):
        if 2 * L in by_L:
            g = by_L[2 * L]["z0_one_photon"] / by_L[L]["z0_one_photon"]
            doubling.append({"L": L, "g0_photon": g, "eta_photon": 1 - g / 2})
    check = {"L": 8, "E(k=1)": e1(8, 1), "E(k=2 along one axis)": e1(8, 2), "measured_README": [0.70, 1.33]}
    out = {"formula": "z0 = 2 L asinh(sin(pi/L)) (one photon); x2 at zero momentum; z_e = g^2/2 frozen",
           "limit_one_photon": 2 * math.pi, "limit_two_photon": 4 * math.pi,
           "rows": rows, "doubling": doubling, "check_against_existing_U1_data": check}
    print(json.dumps(out, indent=1))
    if len(sys.argv) > 1:
        with open(sys.argv[1], "w") as f:
            json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
