"""The existence TTL read from the lattice data (README §3.1b, finding MG7), and the two-witness (reflection-positivity) check.

TTL: a certificate's time to live is the inverse of the energy of the lightest state that carries it, TTL = 1 / (a E) in grid ticks
(Delta = hbar / TTL). For SU(2), the scalar glueball: also in units of the string tension, TTL * sqrt(sigma) = 1 / (m / sqrt(sigma)).
For U(1), the photon at the smallest momentum of the box.

Two witnesses: Axiom 1's pair reads, in physics, as reflection positivity (a configuration and its mirror image always pair
positively), the property that makes one tick of renewal a positive transfer matrix. It implies that every correlator matrix
C_ij(t) = <O_i(t) O_j(0)> of time-slice operators is positive semidefinite for every t. Checked here on the stored glueball and torelon
operators: the smallest eigenvalue of C(t), with its jackknife error.

Usage: python ttl.py ../results/lattice_summary.json ../results/su2_*.npz
"""

import json
import sys

import numpy as np

from analyse import correlator_matrix, jackknife


def ttl_table(summary):
    print("TTL of the lightest certificate")
    for r in summary:
        if r.get("group") == "U(1)":
            e, de = r["E_p1_used"]
            print(f"  U(1)  beta={r['beta']:.1f} L={r['L']:2d}: E1 = {e:.3f} +- {de:.3f}  TTL = {1 / e:.2f} +- {de / e ** 2:.2f} ticks"
                  f"   (TTL / L = {1 / e / r['L']:.3f})")
        elif "a_m_0pp" in r:
            m, dm = r["a_m_0pp"]
            q, dq = r["m_0pp_over_sqrt_sigma"]
            print(f"  SU(2) beta={r['beta']:.1f} L={r['L']:2d}: TTL = {1 / m:.2f} +- {dm / m ** 2:.2f} ticks,"
                  f"  TTL * sqrt(sigma) = {1 / q:.3f} +- {dq / q ** 2:.3f}")


def rp_check(path, tmax=4):
    d = np.load(path)
    print(f"Two-witness check (reflection positivity), {path.split('/')[-1]}: smallest eigenvalue of C(t) / largest of C(0)")
    for name in ("glue", "tor"):
        ops = d[name]

        def fn(x):
            C = correlator_matrix(x)
            scale = np.linalg.eigvalsh(C[0])[-1]
            return np.array([np.linalg.eigvalsh(C[t])[0] / scale for t in range(tmax + 1)])

        v, e = jackknife(ops, fn)
        cells = "  ".join(f"t={t}: {v[t]:+.2e} +- {e[t]:.1e}" for t in range(tmax + 1))
        bad = [t for t in range(tmax + 1) if v[t] < -2 * e[t]]
        print(f"  {name:4s} {cells}   {'NEGATIVE beyond 2 errors at t=' + str(bad) if bad else 'positive within errors'}")


if __name__ == "__main__":
    ttl_table(json.load(open(sys.argv[1], encoding="utf-8")))
    for p in sys.argv[2:]:
        rp_check(p)
