"""The TTL scan's analysis (PREREG-TTL.md): analyse.py's correlators and variational step, with a plateau rule instead of a fixed time.

For each channel (scalar glueball, torelon) the effective mass m(t) = ln[c(t)/c(t+1)] of the variationally best operator is computed with
jackknife errors. The plateau time t* is the smallest t >= 1 at which m(t) agrees with both m(t+1) and m(t+2) within their combined errors
(|m(t) - m(t+k)| <= sqrt(e(t)^2 + e(t+k)^2), k = 1, 2) and e(t) <= 0.25 m(t); the mass is m(t*). String tension from the torelon as in analyse.py (Teper's eqn 6). TTL = 1 / (a m_0++) in ticks, TTL * sqrt(sigma) in
real units.

Usage: python analyse_plateau.py RUN.npz [RUN.npz ...]   (prints one JSON list)
"""

import json
import sys

import numpy as np

from analyse import correlator_matrix, best_projection, effective_masses, jackknife


def meff(ops, tmax=8):
    def fn(x):
        C = correlator_matrix(x)
        v = best_projection(C)
        _, m = effective_masses(C, v, tmax=tmax)
        return m
    return jackknife(ops, fn)


def plateau(m, e):
    for t in range(1, len(m) - 2):
        if not (np.all(np.isfinite(m[t:t + 3])) and m[t] > 0):
            continue
        if e[t] <= 0.25 * m[t] and all(abs(m[t] - m[t + k]) <= np.hypot(e[t], e[t + k]) for k in (1, 2)):
            return t
    return None


def analyse(path):
    d = np.load(path)
    L, beta = int(d["L"]), float(d["beta"])
    out = {"beta": beta, "L": L, "n_meas": int(d["plaq"].shape[0]), "levels": [int(x) for x in d["smear_levels"]]}
    mg, eg = meff(d["glue"])
    mt, et = meff(d["tor"])
    out["glueball_meff"] = [[float(a), float(b)] for a, b in zip(mg, eg)]
    out["torelon_meff"] = [[float(a), float(b)] for a, b in zip(mt, et)]
    tg, tt = plateau(mg, eg), plateau(mt, et)
    out["t_glueball"], out["t_torelon"] = tg, tt
    if tg is None or tt is None:
        out["verdict"] = "no plateau"
        return out
    aml, daml = float(mt[tt]), float(et[tt])
    a2s = (aml + np.pi / (3 * L)) / L
    asq = float(np.sqrt(a2s))
    dasq = float(daml / L / (2 * asq))
    amg, damg = float(mg[tg]), float(eg[tg])
    ratio = amg / asq
    dratio = ratio * np.hypot(damg / amg, dasq / asq)
    out.update({"torelon_mass": [aml, daml], "a_sqrt_sigma": [asq, dasq], "a_m_0pp": [amg, damg], "m_0pp_over_sqrt_sigma": [ratio, dratio],
                "ttl_ticks": [1 / amg, damg / amg ** 2], "ttl_sqrt_sigma": [1 / ratio, dratio / ratio ** 2]})
    return out


if __name__ == "__main__":
    print(json.dumps([analyse(p) for p in sys.argv[1:]], indent=1))
