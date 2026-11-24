"""Turn the raw data of run_su2.py / run_u1.py into masses with jackknife errors.

Method (the standard one, as in Teper's review hep-th/9812187, Appendix A): vacuum-subtracted zero-momentum correlators of several
smeared operators, a variational (generalised eigenvalue) step at t = 0 and t = a to pick the best operator, and the effective mass
from t = a to t = 2a. For the torelon (flux closed around the box, length L), the string tension follows from
a m_l = a^2 sigma L - pi / (3 L) (Teper's eqn 6).
"""

import json
import sys

import numpy as np


def correlator_matrix(ops):
    """ops: (n_meas, n_ops, T). Returns C[t, i, j] averaged over sources and measurements, vacuum subtracted."""
    o = ops - ops.mean(axis=(0, 2), keepdims=True)
    n, k, T = o.shape
    C = np.zeros((T // 2 + 1, k, k))
    for t in range(T // 2 + 1):
        C[t] = np.einsum("mis,mjs->ij", o, np.roll(o, -t, axis=2)) / (n * T)
    return 0.5 * (C + np.transpose(C, (0, 2, 1)))


def best_projection(C, t0=0, t1=1):
    """Generalised eigenvalue problem C(t1) v = lambda C(t0) v; the vector of the largest lambda (the lightest state)."""
    A = C[t0]
    w, U = np.linalg.eigh(A)
    keep = w > w.max() * 1e-10
    Ah = U[:, keep] / np.sqrt(w[keep])
    M = Ah.T @ C[t1] @ Ah
    lw, lv = np.linalg.eigh(M)
    v = Ah @ lv[:, -1]
    return v


def effective_masses(C, v, tmax=4):
    c = np.array([v @ C[t] @ v for t in range(min(tmax + 2, C.shape[0]))])
    with np.errstate(invalid="ignore", divide="ignore"):
        m = np.log(c[:-1] / c[1:])
    return c, m


def jackknife(ops, fn, nbins=20):
    """fn maps an (n, k, T) block to an array; returns mean (on all data) and jackknife error over nbins contiguous bins."""
    n = ops.shape[0]
    nb = min(nbins, n)
    edges = np.linspace(0, n, nb + 1).astype(int)
    full = fn(ops)
    reps = []
    for b in range(nb):
        mask = np.ones(n, bool)
        mask[edges[b]:edges[b + 1]] = False
        reps.append(fn(ops[mask]))
    reps = np.array(reps)
    err = np.sqrt((nb - 1) / nb * np.sum((reps - reps.mean(axis=0)) ** 2, axis=0))
    return full, err


def mass_at(ops, t):
    def fn(x):
        C = correlator_matrix(x)
        v = best_projection(C)
        _, m = effective_masses(C, v)
        return m
    m, e = jackknife(ops, fn)
    return m, e


def analyse_su2(path):
    d = np.load(path)
    L, T, beta = int(d["L"]), int(d["T"]), float(d["beta"])
    out = {"beta": beta, "L": L, "T": T, "n_meas": int(d["plaq"].shape[0])}
    p = d["plaq"]
    nb = 20
    pb = p[: len(p) // nb * nb].reshape(nb, -1).mean(axis=1)
    out["plaquette"] = [float(p.mean()), float(pb.std(ddof=1) / np.sqrt(nb))]
    tor = d["tor"]  # (n, n_smear, T)
    mt, et = mass_at(tor, 1)
    glue = d["glue"]  # (n, n_ops, T)
    mg, eg = mass_at(glue, 1)
    # Teper: effective mass from t = a to 2a for beta <= 2.5 (index 1), from 2a to 3a above.
    ti = 1 if beta <= 2.5 else 2
    aml, daml = float(mt[ti]), float(et[ti])
    a2s = (aml + np.pi / (3 * L)) / L
    asq = float(np.sqrt(a2s))
    dasq = float(daml / L / (2 * asq))
    amg, damg = float(mg[ti]), float(eg[ti])
    out.update({
        "torelon_meff": [[float(x), float(y)] for x, y in zip(mt, et)],
        "glueball_meff": [[float(x), float(y)] for x, y in zip(mg, eg)],
        "a_sqrt_sigma": [asq, dasq],
        "a_m_0pp": [amg, damg],
        "m_0pp_over_sqrt_sigma": [amg / asq, amg / asq * np.hypot(damg / amg, dasq / asq)],
        "t_index_used": ti,
    })
    return out


def cosh_mass(c, t, T):
    """Solve c(t)/c(t+1) = cosh(E (T/2 - t)) / cosh(E (T/2 - t - 1)) for E (a state propagating both ways round periodic time)."""
    r = c[t] / c[t + 1]
    if not np.isfinite(r) or r <= 1:
        return np.nan
    lo, hi = 1e-6, 10.0
    f = lambda E: np.cosh(E * (T / 2 - t)) / np.cosh(E * (T / 2 - t - 1)) - r
    if f(lo) > 0 or f(hi) < 0:
        return np.nan
    for _ in range(100):
        mid = 0.5 * (lo + hi)
        if f(mid) > 0:
            hi = mid
        else:
            lo = mid
    return 0.5 * (lo + hi)


def analyse_u1(path, t_use=1):
    """Photon energy at the smallest momenta, against the free massless lattice dispersion 2 asinh(sin(pi n / L))."""
    d = np.load(path)
    L, T, beta = int(d["L"]), int(d["T"]), float(d["beta"])
    ops = d["ops"]  # (n, n_mom, n_ops, 3, T) complex
    n = ops.shape[0]
    out = {"group": "U(1)", "beta": beta, "L": L, "T": T, "n_meas": n}
    p = d["plaq"]
    nb = 20
    pb = p[: len(p) // nb * nb].reshape(nb, -1).mean(axis=1)
    out["plaquette"] = [float(p.mean()), float(pb.std(ddof=1) / np.sqrt(nb))]
    for a, nm in enumerate((1, 2)):
        x = ops[:, a]  # (n, n_ops, 3, T)

        def fn(y):
            k = y.shape[1]
            C = np.zeros((T // 2 + 1, k, k))
            for t in range(T // 2 + 1):
                C[t] = np.real(np.einsum("mipt,mjpt->ij", np.roll(y, -t, axis=3), np.conj(y))) / (y.shape[0] * 3 * T)
            C = 0.5 * (C + np.transpose(C, (0, 2, 1)))
            v = best_projection(C)
            c = np.array([v @ C[t] @ v for t in range(T // 2 + 1)])
            return np.array([cosh_mass(c, t, T) for t in range(T // 2)])

        m, e = jackknife(x, fn)
        out[f"E_p{nm}"] = [[float(u), float(v)] for u, v in zip(m, e)]
        out[f"E_p{nm}_used"] = [float(m[t_use]), float(e[t_use])]
        out[f"E_free_p{nm}"] = float(2 * np.arcsinh(np.sin(np.pi * nm / L)))
    return out


if __name__ == "__main__":
    res = []
    for p in sys.argv[1:]:
        res.append(analyse_u1(p) if "u1_" in p.split("/")[-1] else analyse_su2(p))
    print(json.dumps(res, indent=1))
