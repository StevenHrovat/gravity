"""c6c-floor: is the act z(L) = L * E(L) super-additive?  Pre-registered in PREREG.md (run once).

Models: 2D Ising strip transfer matrix (brute force), free photon box (closed formula), Dirichlet massive scalar (closed formula).
numpy only; one process.
"""
import json
import math
import time

import numpy as np

LMAX = 12
LS = list(range(2, LMAX + 1))


def ising_strip_gaps(L, K, periodic):
    n = 2 ** L
    idx = np.arange(n)
    bits = ((idx[:, None] >> np.arange(L)[None, :]) & 1) * 2 - 1  # spins +-1, shape (n, L)
    # intra-row energy
    if periodic:
        intra = np.sum(bits * np.roll(bits, -1, axis=1), axis=1)
    else:
        intra = np.sum(bits[:, :-1] * bits[:, 1:], axis=1)
    d_half = np.exp(0.5 * K * intra)
    # inter-row: prod_i exp(K s_i s'_i) = exp(K * (L - 2 * hamming))
    t = np.array([[math.exp(K), math.exp(-K)], [math.exp(-K), math.exp(K)]])
    T = np.array([[1.0]])
    for _ in range(L):
        T = np.kron(T, t)
    # kron ordering: first factor is the most significant bit; our bit i is (idx >> i) & 1, symmetric in i, so ordering does not
    # matter for T (all factors equal).
    V = d_half[:, None] * T * d_half[None, :]
    half = n // 2
    a = np.arange(half)  # states with top bit 0
    comp = (n - 1) - a
    Vev = V[np.ix_(a, a)] + V[np.ix_(a, comp)]
    Vodd = V[np.ix_(a, a)] - V[np.ix_(a, comp)]
    ev = np.sort(np.linalg.eigvalsh(Vev))[::-1]
    od = np.sort(np.linalg.eigvalsh(Vodd))[::-1]
    lam0 = ev[0]
    E_odd = math.log(lam0 / od[0])
    E_even = math.log(lam0 / ev[1])
    return E_odd, E_even


def defects(z):
    """z: dict L -> z(L). Returns violations (D > 1e-9), max defect c on the range, one-box criterion."""
    viol = []
    cmax = -math.inf
    keys = sorted(z)
    for L1 in keys:
        for L2 in keys:
            if L2 < L1 or (L1 + L2) not in z:
                continue
            D = z[L1] + z[L2] - z[L1 + L2]
            cmax = max(cmax, D)
            if D > 1e-9:
                viol.append([L1, L2, D])
    c = max(cmax, 0.0)
    crit = [L for L in keys if z[L] > c]
    return {"n_violations": len(viol), "violations_first5": viol[:5], "c_on_range": c,
            "criterion_L0_with_z_gt_c": crit}


def main():
    t0 = time.time()
    out = {"ising": {}, "photon": {}, "dirichlet_scalar": {}}
    for K in (0.25, 0.6):
        Kstar = math.atanh(math.exp(-2 * K))
        m_inf = 2 * (Kstar - K) if K < 0.5 * math.log(1 + math.sqrt(2)) else None
        for periodic in (True, False):
            key = f"K={K},{'periodic' if periodic else 'free'}"
            Eo, Ee = {}, {}
            for L in LS:
                Eo[L], Ee[L] = ising_strip_gaps(L, K, periodic)
            zo = {L: L * Eo[L] for L in LS}
            ze = {L: L * Ee[L] for L in LS}
            out["ising"][key] = {
                "m_inf_odd_onsager": m_inf,
                "E_odd": Eo, "E_even": Ee,
                "E_odd_minus_m": ({L: Eo[L] - m_inf for L in LS} if m_inf else None),
                "odd": defects(zo), "even": defects(ze),
            }
            print(key, "E_odd", {L: round(Eo[L], 5) for L in LS})
            print(key, "E_even", {L: round(Ee[L], 5) for L in LS})
            print(key, "odd:", out["ising"][key]["odd"]["n_violations"], "violations, c =",
                  round(out["ising"][key]["odd"]["c_on_range"], 5),
                  "crit L0:", out["ising"][key]["odd"]["criterion_L0_with_z_gt_c"])
            print(key, "even:", out["ising"][key]["even"]["n_violations"], "violations, c =",
                  round(out["ising"][key]["even"]["c_on_range"], 5),
                  "crit L0:", out["ising"][key]["even"]["criterion_L0_with_z_gt_c"])
    # photon, closed formula
    zph = {L: 2 * L * math.asinh(math.sin(math.pi / L)) for L in LS}
    out["photon"]["range"] = {"z0": zph, **defects(zph)}
    big = [2 ** k for k in range(1, 13)]
    zbig = {L: 2 * L * math.asinh(math.sin(math.pi / L)) for L in big}
    cbig = max(zbig[a] + zbig[b] - zbig[a + b] for a in big for b in big if a + b in zbig)
    out["photon"]["dyadic_to_4096"] = {"c": cbig, "two_pi": 2 * math.pi, "max_z0": max(zbig.values()),
                                       "criterion_holds": max(zbig.values()) > cbig}
    print("photon range:", out["photon"]["range"]["n_violations"], "violations; c(range) =",
          round(out["photon"]["range"]["c_on_range"], 4), "crit:", out["photon"]["range"]["criterion_L0_with_z_gt_c"])
    print("photon dyadic to 4096: c =", round(cbig, 4), "max z0 =", round(max(zbig.values()), 4))
    # Dirichlet massive scalar, m = 1, continuum grid
    grid = [0.25 * k for k in range(1, 49)]
    zd = {round(L, 2): math.sqrt(L * L + math.pi ** 2) for L in grid}
    viol = sum(1 for a in grid for b in grid if round(a + b, 2) in zd and zd[round(a, 2)] + zd[round(b, 2)] - zd[round(a + b, 2)] > 0)
    tot = sum(1 for a in grid for b in grid if round(a + b, 2) in zd)
    out["dirichlet_scalar"] = {"pairs": tot, "violations": viol,
                               "E_minus_m_at_L=4": math.sqrt(16 + math.pi ** 2) / 4 - 1}
    print("dirichlet scalar: violations", viol, "of", tot)
    out["runtime_s"] = time.time() - t0
    with open("superadd_check.json", "w") as f:
        json.dump(out, f, indent=1, default=float)
    print("runtime", round(out["runtime_s"], 1), "s")


if __name__ == "__main__":
    main()
