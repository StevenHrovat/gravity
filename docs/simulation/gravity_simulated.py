"""GUID v6: Our theory as simulated. Gravity as a classical, recorded frame acting on quantum matter (measure-and-prepare, measurement
and feedback), run side by side with its quantum-gravity alternative (a coherent field), at scale. Every number the simulation paper may
quote is computed here from named inputs and written to results/gravity_simulated.json.

Run: python3 docs/simulation/gravity_simulated.py   (numpy, scipy; deterministic: fixed seeds, BLAS pinned to one thread; a few minutes).
Each check prints OK or FAIL with got and expected; the last line counts them; the exit code is 0 only if all pass. Misses are findings.

Units in G1: lengths in units of the spacing d, phases per unit time in omega0 = G m^2 / (hbar d). Physical instance: Bose et al. (2017),
m = 1e-14 kg, dx = 250 um, d = 450 um, diamond sphere of radius R = 0.88 um (omega0 = 0.141 rad/s, lambda = G m^2/(hbar R) = 72 /s).

  [G1] many gravitating quantum masses on a line, each a two-level system split by dx:
       (a) coherent field (quantum gravity): exact statevector 2^(-N/2) sum_s exp(i sum_{i<j} phi_ij(s)) |s> up to N = 24 (an IQP circuit):
           half-chain entropy against the Page value, all pairwise negativities (statevector and an exact two-body formula, which also runs at
           N = 4000), the collision probability Z = 2^N sum_x p(x)^2 of the X-basis output against Porter-Thomas (Z -> 2, third moment -> 6)
       (b) recorded frame (GUID): every mass is continuously measured at the Bridge-B rate, the field each mass feels is the Newtonian field of
           the others' records (measurement and feedback, balance rule at equality); N = 4000 masses, O(N^2) per step: coherence decays as
           exp(-lambda t), product states per trajectory, mean force = direct Newtonian sum, X-basis Z = prod_j (1 + <sigma_x>_j^2);
           small N: the averaged (feedback master equation) state is separable for every measurement strength; cost against 2^N
  [G2] Bose-Marletto-Vedral under (Q), (Q+DP) and (G): negativity and witnesses against time; rho = R [1/(d-dx) + 1/(d+dx) - 2/d] is
       mass-independent; its supremum over geometries; the Diosi-Penrose self-energy of displaced spheres checked by quadrature; the exact
       entanglement threshold omega/lambda = 2 under independent dephasing (and about sqrt 2 with the full Diosi-Penrose kernel)
  [G3] classical-quantum toy: qubit (Lindblad sigma_z) coupled to a classical momentum p, discretised in p; positivity holds iff
       D1^2 <= 4 D0 D2 in this normalisation, which is Oppenheim et al. Eq. (23) after mapping; equality = measurement-feedback unravelling
  [G4] two coupled oscillators, exact Gaussian covariance evolution: quantum coupling entangles; the Kafri-Taylor-Milburn classical channel
       (measure x_i at strength k, feed back K x_i) never does, its mean dynamics match, its heating k + K^2/(4k) is minimal (= K) at k = K/2
"""

import os

for _v in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"   # deterministic BLAS, and far faster than oversubscribed threads on a shared machine

import json
import math
import platform
import time
from pathlib import Path

import numpy as np
import scipy
from scipy import integrate, optimize, sparse
from scipy.linalg import expm
from scipy.sparse.linalg import expm_multiply
from scipy.special import digamma

T_START = time.perf_counter()
OUT = Path(__file__).resolve().parent / "results" / "gravity_simulated.json"
results = []
RES = {"meta": {}, "checks": []}


def check(label, got, want, rtol=1e-6, atol=0.0):
    got, want = float(got), float(want)
    ok = abs(got - want) <= max(atol, rtol * abs(want))
    print(f"{'OK  ' if ok else 'FAIL'} {label}: {got:.6g} (expected {want:.6g})", flush=True)
    results.append(ok)
    RES["checks"].append({"label": label, "ok": ok, "got": got, "expected": want, "rtol": rtol, "atol": atol})


def check_true(label, cond):
    print(f"{'OK  ' if cond else 'FAIL'} {label}", flush=True)
    results.append(bool(cond))
    RES["checks"].append({"label": label, "ok": bool(cond)})


def fl(x):
    """JSON-safe numbers (recursively)."""
    if isinstance(x, dict):
        return {str(k): fl(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [fl(v) for v in x]
    if isinstance(x, np.ndarray):
        return fl(x.tolist())
    if isinstance(x, (np.floating, float)):
        return float(x) if math.isfinite(x) else str(x)
    if isinstance(x, (np.integer,)):
        return int(x)
    if isinstance(x, (np.bool_,)):
        return bool(x)
    if isinstance(x, complex):
        return [x.real, x.imag]
    return x


# Constants: SI 2019 exact values, CODATA 2018 (as docs/quantum-gravity/checks.py).
h_pl = 6.62607015e-34
hbar = h_pl / (2 * math.pi)
G = 6.67430e-11
# Physical instance: Bose et al. (2017).
m_b, d_b, dx_b, rho_dia = 1e-14, 450e-6, 250e-6, 3510.0
R_b = (3 * m_b / (4 * math.pi * rho_dia)) ** (1 / 3)
GM2H = G * m_b**2 / hbar                     # m/s; a phase rate is GM2H / distance
omega0 = GM2H / d_b                          # rad/s, the G1 phase unit
lam_B = GM2H / R_b                           # 1/s, Bridge B (Diosi-Penrose rate in the paper's convention)
DELTA = dx_b / d_b                           # split over spacing, 5/9
S4 = [(a, b) for a in (0, 1) for b in (0, 1)]


# ------------------------------------------------------------------------------------------------------------------------- helpers
def neg_pt_min(rho):
    """Smallest eigenvalue of the partial transpose (second qubit) of a batch (..., 4, 4) of two-qubit states."""
    sh = rho.shape
    pt = rho.reshape(sh[:-2] + (2, 2, 2, 2)).swapaxes(-1, -3).reshape(sh)
    return np.linalg.eigvalsh(pt)[..., 0]


def negativity(rho):
    """Negativity sum of |negative eigenvalues| of the partial transpose (batch)."""
    sh = rho.shape
    pt = rho.reshape(sh[:-2] + (2, 2, 2, 2)).swapaxes(-1, -3).reshape(sh)
    ev = np.linalg.eigvalsh(pt)
    return -np.where(ev < 0, ev, 0.0).sum(axis=-1)


def bits(N):
    """Branch table s[index, qubit], qubit 0 = most significant bit (the axis order of psi.reshape([2]*N))."""
    return ((np.arange(2**N)[:, None] >> (N - 1 - np.arange(N))[None, :]) & 1).astype(float)


def chain_couplings(N, delta=DELTA):
    """Ising form of sum_{i<j} 1/|x_i - x_j| on a line, x_i = i + (s_i - 1/2) delta (units of d):
    Omega(s) = const + sum_i h_i s_i + sum_{i<j} J_ij s_i s_j, with J_ij = -g(|i-j|), g(n) = 2 delta^2 / (n (n^2 - delta^2))."""
    n = np.arange(1, N, dtype=float)
    cm = 1 / (n - delta) - 1 / n               # left member of a pair moves towards the right one in its branch 1
    cp = 1 / (n + delta) - 1 / n               # right member moves away
    h = np.zeros(N)
    h[: N - 1] += np.cumsum(cm)[::-1]          # mass i has partners at distances 1..N-1-i on its right
    h[1:] += np.cumsum(cp)                     # and 1..i on its left
    gtab = np.concatenate([[0.0], -2 * delta**2 / (n * (n * n - delta**2))])
    idx = np.arange(N)
    J = gtab[np.abs(idx[:, None] - idx[None, :])]
    return h, J


def energy_table(h, J):
    """Omega(s) - const for all 2^N branches, built by doubling (qubit 0 most significant)."""
    N = len(h)
    E = np.zeros(1)
    for k in range(N):
        lin = np.zeros(1)
        for i in range(k):
            lin = np.stack([lin, lin + J[i, k]], axis=-1).reshape(-1)
        E = np.stack([E, E + h[k] + lin], axis=-1).reshape(-1)
    return E


def fwht(a):
    """H^{(x)N} applied to a statevector (in place on a copy)."""
    N = int(round(math.log2(a.size)))
    a = a.copy()
    for k in range(N):
        v = a.reshape(2**k, 2, 2 ** (N - k - 1))
        x = v[:, 0, :] + v[:, 1, :]
        v[:, 1, :] = v[:, 0, :] - v[:, 1, :]
        v[:, 0, :] = x
    a *= 2 ** (-N / 2)
    return a


def x_moments(psi):
    """Z = 2^N sum p^2 and M3 = 2^(2N) sum p^3 of the X-basis output distribution (Porter-Thomas: 2 and 6)."""
    N = int(round(math.log2(psi.size)))
    p = np.abs(fwht(psi)) ** 2
    return 2.0**N * np.dot(p, p), 4.0**N * np.sum(p**3)


def half_entropy(psi):
    N = int(round(math.log2(psi.size)))
    M = psi.reshape(2 ** (N // 2), -1)
    ev = np.linalg.eigvalsh(M @ M.conj().T)
    ev = ev[ev > 1e-16]
    return float(-(ev * np.log2(ev)).sum())


def page_bits(nA, nB):
    """Page's mean entanglement entropy of a random pure state, in bits (d_A <= d_B)."""
    dA, dB = 2.0 ** min(nA, nB), 2.0 ** max(nA, nB)
    return (digamma(dA * dB + 1) - digamma(dB + 1) - (dA - 1) / (2 * dB)) / math.log(2)


def pair_rho_sv(psi, N, i, j):
    A = np.moveaxis(psi.reshape([2] * N), (i, j), (0, 1)).reshape(4, -1)
    return A @ A.conj().T


def pair_rho_exact(h, J, tau, pairs):
    """Exact two-body marginals of 2^(-N/2) sum_s exp(i tau Omega(s)) |s>: the sum over the other masses factorises,
    rho_ij[(a,b),(a',b')] = 1/4 exp(i tau [e(a,b) - e(a',b')]) prod_{k != i,j} (1 + exp(i tau [J_ik (a-a') + J_jk (b-b')])) / 2."""
    pi_ = np.array([p[0] for p in pairs])
    pj_ = np.array([p[1] for p in pairs])
    fac = {}
    with np.errstate(divide="ignore"):
        for da, db in ((1, 0), (0, 1), (1, 1), (1, -1)):
            out = np.empty(len(pairs), complex)
            for c0 in range(0, len(pairs), 256):
                sl = slice(c0, c0 + 256)
                th = tau * (J[pi_[sl]] * da + J[pj_[sl]] * db)
                rows = np.arange(th.shape[0])
                th[rows, pi_[sl]] = 0.0
                th[rows, pj_[sl]] = 0.0
                cs = np.cos(th / 2)
                out[sl] = np.prod(np.sign(cs), axis=1) * np.exp(np.log(np.abs(cs)).sum(axis=1) + 0.5j * th.sum(axis=1))
            fac[(da, db)] = out
    Jij = J[pi_, pj_]
    rho = np.empty((len(pairs), 4, 4), complex)
    for A, (a, b) in enumerate(S4):
        for B, (a2, b2) in enumerate(S4):
            da, db = a - a2, b - b2
            if (da, db) == (0, 0):
                f = 1.0
            elif (da, db) in fac:
                f = fac[(da, db)]
            else:
                f = np.conj(fac[(-da, -db)])
            e = h[pi_] * (a - a2) + h[pj_] * (b - b2) + Jij * (a * b - a2 * b2)
            rho[:, A, B] = 0.25 * np.exp(1j * tau * e) * f
    return rho


def sech(x):
    ax = np.abs(x)
    e = np.exp(-ax)
    return 2 * e / (1 + e * e)


def reduce_state(rho, N, keep):
    t = rho.reshape([2] * (2 * N))
    ins = list(range(2 * N))
    for q in range(N):
        if q not in keep:
            ins[N + q] = ins[q]
    outs = list(keep) + [N + q for q in keep]
    k = len(keep)
    return np.einsum(t, ins, outs).reshape(2**k, 2**k)


def pt_min_subset(rho, N, subset):
    t = rho.reshape([2] * (2 * N))
    perm = list(range(2 * N))
    for q in subset:
        perm[q], perm[N + q] = perm[N + q], perm[q]
    return np.linalg.eigvalsh(t.transpose(perm).reshape(2**N, 2**N))[0]


RES["meta"] = {"script": "docs/simulation/gravity_simulated.py", "python": platform.python_version(), "numpy": np.__version__,
               "scipy": scipy.__version__, "blas_threads": 1, "units_G1": "lengths in d, phase rates in omega0 = G m^2/(hbar d)",
               "instance": {"m_kg": m_b, "d_m": d_b, "dx_m": dx_b, "diamond_density": rho_dia, "R_m": R_b, "omega0_rad_s": omega0,
                            "lambda_B_per_s": lam_B, "lambda_over_omega0": lam_B / omega0}}

# =================================================================================================================================
print("\n[G1a] Many gravitating masses with a coherent (quantised) field: exact statevector, an IQP circuit")
G1 = RES["G1"] = {"a": {}, "b": {}, "cost": {}}
g1 = 2 * DELTA**2 / (1 - DELTA**2)          # nearest-neighbour entangling rate in omega0
tau_pi = math.pi / g1                       # an isolated pair would be maximally entangled here
check("R of the 1e-14 kg diamond sphere, um", R_b * 1e6, 0.88, rtol=1e-2)
check("phase unit omega0 = G m^2/(hbar d), rad/s", omega0, 0.1406, rtol=2e-3)
check("nearest-neighbour entangling rate g(1) omega0 = the Bose et al. rate 0.1256 rad/s (checks.py Q5)", g1 * omega0, 0.1256, rtol=2e-3)
check("Bridge-B rate G m^2/(hbar R) = 72 /s (checks.py Q19)", lam_B, 72, rtol=1e-2)
h8, J8 = chain_couplings(8)
s8 = bits(8)
x8 = np.arange(8)[None, :] + (s8 - 0.5) * DELTA
E8_direct = sum(1 / np.abs(x8[:, i] - x8[:, j]) for i in range(8) for j in range(i + 1, 8))
E8 = energy_table(h8, J8)
check("Ising table h.s + sum J s s equals the direct sum of 1/|x_i - x_j| over all 256 branches (up to a constant)",
      np.ptp(E8_direct - E8), 0, atol=1e-12)
G1["a"]["g1"] = g1
G1["a"]["tau_pi"] = tau_pi
G1["a"]["tau_pi_seconds"] = tau_pi / omega0

TAU_Z = [0.5, tau_pi, 10.0, 100.0, 1e3, 1e5]
NS = [8, 10, 12, 14, 16, 18, 20, 22, 24]
TAU_S = sorted(set(np.round(np.geomspace(0.1, 1e7, 22), 6).tolist() + [tau_pi]))
TAU_LONG = np.geomspace(1e4, 1e7, 12)
zN, entropy, longrun, timing = {}, {}, {}, {}
store_psi = {}
for N in NS:
    t0 = time.perf_counter()
    h, J = chain_couplings(N)
    E = energy_table(h, J)
    t_table = time.perf_counter() - t0
    zrow, tstate = {}, []
    for tau in TAU_Z:
        t1 = time.perf_counter()
        psi = np.exp(1j * tau * E) * 2 ** (-N / 2)
        Z, M3 = x_moments(psi)
        tstate.append(time.perf_counter() - t1)
        zrow[f"{tau:.6g}"] = {"Z": Z, "M3": M3}
        del psi
    zN[N] = zrow
    timing[N] = {"table_s": t_table, "state_plus_Z_s_median": float(np.median(tstate))}
    if N in (12, 16, 20):
        srow = {}
        for tau in TAU_S:
            srow[f"{tau:.6g}"] = half_entropy(np.exp(1j * tau * E) * 2 ** (-N / 2))
        entropy[N] = srow
        zs, m3s, ss = [], [], []
        for tau in TAU_LONG:
            psi = np.exp(1j * tau * E) * 2 ** (-N / 2)
            Z, M3 = x_moments(psi)
            zs.append(Z), m3s.append(M3), ss.append(half_entropy(psi))
        longrun[N] = {"Z_mean": np.mean(zs), "Z_sem": np.std(zs, ddof=1) / math.sqrt(len(zs)), "M3_mean": np.mean(m3s),
                      "S_mean_bits": np.mean(ss), "S_page_bits": page_bits(N // 2, N // 2)}
    if N in (22, 24):
        srow = {}
        for tau in ([tau_pi, 1e3, 1e5] if N == 22 else [tau_pi, 1e5]):
            t1 = time.perf_counter()
            srow[f"{tau:.6g}"] = half_entropy(np.exp(1j * tau * E) * 2 ** (-N / 2))
            timing[N]["entropy_s"] = time.perf_counter() - t1
        entropy[N] = srow
    if N == 24:
        zs, m3s = [], []
        for tau in (1e5, 1e6, 1e7):
            Z, M3 = x_moments(np.exp(1j * tau * E) * 2 ** (-N / 2))
            zs.append(Z), m3s.append(M3)
        longrun[N] = {"Z_mean": np.mean(zs), "Z_sem": np.std(zs, ddof=1) / math.sqrt(len(zs)), "M3_mean": np.mean(m3s),
                      "S_mean_bits": entropy[24]["100000"], "S_page_bits": page_bits(12, 12), "taus": [1e5, 1e6, 1e7]}
    if N in (16, 20, 24):
        store_psi[N] = (h, J, E)
    print(f"     N = {N}: table {t_table:.2f} s, state + Z per time {np.median(tstate):.2f} s; Z(tau_pi) = {zrow[f'{tau_pi:.6g}']['Z']:.4g}, "
          f"Z(1e5) = {zrow['100000']['Z']:.4g}", flush=True)
G1["a"]["collision_Z_vs_N_tau"] = zN
G1["a"]["half_chain_entropy_bits"] = entropy
G1["a"]["late_time_average_tau_1e4_1e7"] = longrun

check("t = 0: |+>^N, X outcome certain, Z = 2^N (N = 20)", x_moments(np.full(2**20, 2**-10, complex))[0], 2.0**20, rtol=1e-9)
dz = [abs(longrun[N]["Z_mean"] - 2) for N in (12, 16, 20, 24)]
dm = [abs(longrun[N]["M3_mean"] - 6) for N in (12, 16, 20, 24)]
check_true(f"late times (tau 1e4..1e7): Porter-Thomas emerges with N: |Z - 2| = {', '.join(f'{v:.3f}' for v in dz)} and |M3 - 6| = "
           f"{', '.join(f'{v:.2f}' for v in dm)} for N = 12, 16, 20, 24 (finite-size deviations shrink)", dz[3] < dz[1] and dm[3] < dm[1])
for N in (20, 24):
    lr = longrun[N]
    check(f"late times, N = {N}: Z -> 2 (Porter-Thomas anticoncentration) within 1%", lr["Z_mean"], 2.0, rtol=0.01)
    check(f"late times, N = {N}: third moment 2^(2N) sum p^3 -> 6 (Porter-Thomas) within 5%", lr["M3_mean"], 6.0, rtol=0.05)
for N in (16, 20):
    lr = longrun[N]
    check(f"late times, N = {N}: half-chain entropy -> Page value, bits", lr["S_mean_bits"], lr["S_page_bits"], atol=0.15)
check("N = 24, tau = 1e5: half-chain entropy within 0.15 bit of Page (11.28 bits)", entropy[24]["100000"], page_bits(12, 12), atol=0.15)
check("at tau_pi (t = 25 s) the half-chain entropy is one ebit, the bond across the cut (N = 24)", entropy[24][f"{tau_pi:.6g}"], 1.0, atol=0.03)
zz10 = [zN[N]["10"]["Z"] for N in (8, 12, 16, 20, 24)]
check_true(f"at tau = 10 (t = 71 s) the output is not anticoncentrated: Z grows with N {np.round(zz10, 2).tolist()}",
           all(np.diff(zz10) > 0) and zz10[-1] > 3)
# random-angle IQP reference: for independent uniform angles E[Z] = 2 - 2^-N (derivation in the md)
rng = np.random.default_rng(20261031)
zr = {}
for N in (10, 14):
    vals = []
    for _ in range(60):
        hr = rng.uniform(0, 2 * np.pi, N)
        Jr = np.triu(rng.uniform(0, 2 * np.pi, (N, N)), 1)
        vals.append(x_moments(np.exp(1j * energy_table(hr, Jr + Jr.T)) * 2 ** (-N / 2))[0])
    zr[N] = {"mean": np.mean(vals), "sem": np.std(vals, ddof=1) / math.sqrt(len(vals)), "theory": 2 - 2.0**-N}
    check(f"random-angle IQP, N = {N}, 60 instances: mean Z = 2 - 2^-N within 4 standard errors", zr[N]["mean"], zr[N]["theory"],
          atol=4 * zr[N]["sem"])
G1["a"]["random_IQP_Z"] = zr

# pairwise negativities: statevector against the exact two-body formula
pn = {}
TAU_PK = 1.3                                   # near the peak of nearest-neighbour negativity in the bulk of a chain
for N in (16, 20, 24):
    h, J, E = store_psi[N]
    taus = [TAU_PK, tau_pi, 10.0, 1e3] if N == 16 else ([TAU_PK, tau_pi] if N == 20 else [TAU_PK])
    for tau in taus:
        psi = np.exp(1j * tau * E) * 2 ** (-N / 2)
        if N == 16:
            pairs = [(i, j) for i in range(N) for j in range(i + 1, N)]
        elif N == 20:
            pairs = [(i, i + 1) for i in range(N - 1)] + [(0, 19), (5, 7), (9, 12)]
        else:
            pairs = [(11, 12), (0, 1), (3, 5)]
        rs = np.array([pair_rho_sv(psi, N, i, j) for i, j in pairs])
        rx = pair_rho_exact(h, J, tau, pairs)
        dev = np.abs(rs - rx).max()
        ng = negativity(rs)
        nn = [negativity(rs[k:k + 1])[0] for k, (i, j) in enumerate(pairs) if j == i + 1]
        pn[f"N{N}_tau{tau:.6g}"] = {"max_dev_statevector_vs_exact": dev, "max_neg": ng.max(), "mean_neg": ng.mean(),
                                    "nn_neg_bulk": float(np.median(nn)), "n_pairs": len(pairs),
                                    "n_pairs_entangled": int((ng > 1e-10).sum())}
        del psi
    check(f"N = {N}: two-body marginals from the statevector equal the exact product formula", max(
        v["max_dev_statevector_vs_exact"] for k, v in pn.items() if k.startswith(f"N{N}_")), 0, atol=1e-12)
G1["a"]["pair_negativity"] = pn
p16 = {k: pn[f"N16_tau{k}"] for k in (f"{TAU_PK:.6g}", f"{tau_pi:.6g}", "10", "1000")}
print("     N = 16, all 120 pairs: " + "; ".join(f"tau {k}: max negativity {v['max_neg']:.4f}, entangled pairs {v['n_pairs_entangled']}"
                                                 for k, v in p16.items()), flush=True)
check_true(f"coherent field, N = 16: pairs are entangled early (tau = 1.3, t = 9 s: max negativity {p16['1.3']['max_neg']:.3f}, "
           f"{p16['1.3']['n_pairs_entangled']} of 120 pairs)", p16["1.3"]["max_neg"] > 0.1)
check_true(f"... and every pair is separable at tau_pi and at tau = 1e3 although the half-chain entropy is 1 ebit and then Page: the "
           f"entanglement is multipartite (monogamy), so pairwise negativity is not the witness at scale",
           p16[f"{tau_pi:.6g}"]["n_pairs_entangled"] == 0 and p16["1000"]["n_pairs_entangled"] == 0)
del store_psi

# =================================================================================================================================
print("\n[G1b] The recorded frame (GUID): measurement and feedback at the Bridge-B rate, N = 4000 masses")
NB = 4000
LAM = d_b / R_b                     # lambda in omega0 units (= 511.6 for the instance)
KAP = LAM / 2                       # measurement strength: kappa (sigma_z rho sigma_z - rho) dephases at 2 kappa = lambda
NTRAJ, NSTEP, TB = 16, 200, 4.0 / LAM
G1["b"]["params"] = {"N": NB, "lambda_omega0": LAM, "kappa_omega0": KAP, "n_traj": NTRAJ, "n_steps": NSTEP, "T_omega0": TB,
                     "T_seconds": TB / omega0, "R_used_m": R_b,
                     "model": "measure Z_j at strength kappa (record dY = 2 sqrt(kappa) <Z_j> dt + dW_j); each mass feels the Newtonian field of "
                              "the others' records s_hat_i dt = (dt - dY_i / (2 sqrt kappa)) / 2; exact branch-first sampling of the records"}
t0 = time.perf_counter()
hB, JB = chain_couplings(NB)
idx = np.arange(NB, dtype=float)
nsig = idx[None, :] - idx[:, None]            # row j, column i: i - j
sgn = np.sign(nsig)
Avec, Bmat = [], []
with np.errstate(divide="ignore", invalid="ignore"):
    for sj in (0, 1):
        F0 = sgn / (nsig - sj * DELTA) ** 2         # force on j (branch sj) from i in branch 0, units G m^2 / d^2
        F1 = sgn / (nsig + (1 - sj) * DELTA) ** 2   # from i in branch 1
        np.fill_diagonal(F0, 0.0)
        np.fill_diagonal(F1, 0.0)
        Avec.append(F0.sum(axis=1))
        Bmat.append(F1 - F0)
        del F0, F1
del nsig, sgn
t_setup = time.perf_counter() - t0
# Newtonian force, Born-averaged over all four branch pairs, by direct summation (independent code path) for sampled masses
sample = [0, 1, 2, 17, 500, 1999, 2000, 3500, NB - 3, NB - 2, NB - 1]
FN_direct, FN_scale = [], []
for j in sample:
    tot, sc = 0.0, 0.0
    for i in range(NB):
        if i == j:
            continue
        for sj in (0, 1):
            for si in (0, 1):
                dxx = (i - j) + (si - sj) * DELTA
                tot += 0.25 * math.copysign(1.0, dxx) / dxx**2
                sc += 0.25 / dxx**2
    FN_direct.append(tot)
    FN_scale.append(sc)
FN = 0.5 * (Avec[0] + Avec[1]) + 0.25 * (Bmat[0].sum(axis=1) + Bmat[1].sum(axis=1))   # frame force at the mean records s_hat = 1/2
relF = np.max(np.abs(FN[sample] - np.array(FN_direct)) / np.array(FN_scale))
check("frame force at the mean records equals the direct Newtonian sum (11 sampled masses incl. ends): max |difference| / sum of "
      "|pair forces| (bulk forces cancel to 1e-4 of the pair scale, so this is the meaningful relative error)", relF, 0, atol=1e-13)
check("Newton's third law for the mean force: sum_j F_j / sum_j |F_j|", FN.sum() / np.abs(FN).sum(), 0, atol=1e-12)

rngB = np.random.default_rng(4000)
zt = rngB.choice([1.0, -1.0], size=(NB, NTRAJ))       # Born rule for |+>: branch +-1 with probability 1/2 each
st = (1 - zt) / 2
drift = hB[:, None] + JB @ st                         # relative phase rate of branch 1 given the true records
Bs = [Bm @ st for Bm in Bmat]
sk = math.sqrt(KAP)
dt = TB / NSTEP
W = np.zeros((NB, NTRAJ))
JW = np.zeros((NB, NTRAJ))
impulse = np.zeros((NB, NTRAJ))
checkpoints = {int(round(x * NSTEP / 4)): x for x in (1, 2, 3, 4)}   # t = 1/lambda .. 4/lambda
mag_mean, cp_data = [], {}
S1 = JB.sum(axis=1)
S2 = (JB**2).sum(axis=1)
KB = 25
t_loop = time.perf_counter()
tcur = 0.0
step = 0
for blk in range(NSTEP // KB):
    dWb = rngB.normal(0.0, math.sqrt(dt), size=(NB, NTRAJ, KB))
    flat = dWb.reshape(NB, -1)
    JdW = (JB @ flat).reshape(NB, NTRAJ, KB)
    B0dW = (Bmat[0] @ flat).reshape(NB, NTRAJ, KB)
    B1dW = (Bmat[1] @ flat).reshape(NB, NTRAJ, KB)
    for k in range(KB):
        q1 = 0.5 * (1 - np.tanh(2 * sk * (2 * sk * zt * tcur + W)))   # P(branch 1) of each mass, left point
        impulse += (1 - q1) * (Avec[0][:, None] * dt + Bs[0] * dt - B0dW[:, :, k] / (4 * sk)) \
            + q1 * (Avec[1][:, None] * dt + Bs[1] * dt - B1dW[:, :, k] / (4 * sk))
        W += dWb[:, :, k]
        JW += JdW[:, :, k]
        tcur += dt
        step += 1
        Y = 2 * sk * zt * tcur + W
        mag = 0.5 * sech(2 * sk * Y)                                 # |rho_01| of each mass
        mag_mean.append(mag.mean())
        if step in checkpoints:
            phi = drift * tcur - JW / (4 * sk)
            c = mag * np.exp(-1j * phi)
            # exact ensemble coherence: 1/2 e^{-lambda t} e^{-i h t} prod_i (1 + e^{-i J_ij t})/2 * exp(-sum_i J_ij^2 t / (32 kappa))
            lc = np.log(np.abs(np.cos(JB * tcur / 2))).sum(axis=1)
            ex = 0.5 * np.exp(-LAM * tcur) * np.exp(-1j * hB * tcur) * np.exp(lc - 0.5j * S1 * tcur) * np.exp(-S2 * tcur / (32 * KAP))
            u = c / ex[:, None]
            X = 2 * c.real
            log2Z = np.log2(1 + X**2).sum(axis=0)
            cp_data[checkpoints[step]] = {"t_over_1/lambda": checkpoints[step], "mean_mag": mag.mean(),
                                          "mean_mag_sem": mag.std() / math.sqrt(mag.size),
                                          "theory_mag": 0.5 * math.exp(-LAM * tcur), "u_mean_re": u.mean().real,
                                          "u_mean_im": u.mean().imag, "u_sem": u.std() / math.sqrt(u.size),
                                          "log2Z_mean": log2Z.mean(), "log2Z_traj_min": log2Z.min(), "log2Z_traj_max": log2Z.max()}
t_loop = time.perf_counter() - t_loop
G1["b"]["wall_seconds"] = {"setup_matrices": t_setup, "time_loop": t_loop, "per_step_per_trajectory": t_loop / (NSTEP * NTRAJ)}
G1["b"]["checkpoints"] = cp_data
tt = np.arange(1, NSTEP + 1) * dt
mm = np.array(mag_mean)
fit_mask = (tt > 0.2 / LAM) & (tt < 3.0 / LAM)
slope = np.polyfit(tt[fit_mask], np.log(mm[fit_mask]), 1)[0]
G1["b"]["fitted_decay_rate_over_lambda"] = -slope / LAM
G1["b"]["feedback_extra_rate_over_lambda_bulk"] = float(np.median(S2) / (32 * KAP) / LAM)
print(f"     N = {NB}, {NTRAJ} trajectories x {NSTEP} steps: loop {t_loop:.1f} s ({1e3 * t_loop / (NSTEP * NTRAJ):.2f} ms per step "
      f"per trajectory), matrices {t_setup:.1f} s", flush=True)
check("single-mass coherence decays as exp(-lambda t): fitted rate / lambda (t = 0.2/lambda .. 3/lambda)", -slope / LAM, 1.0, rtol=0.01)
for x, cd in cp_data.items():
    if x <= 3:
        check(f"t = {x}/lambda: mean |rho_01| over 4000 masses x 16 trajectories = exp(-lambda t)/2 (5 standard errors)",
              cd["mean_mag"], cd["theory_mag"], atol=5 * cd["mean_mag_sem"])
        check(f"t = {x}/lambda: complex coherence / exact closed form (incl. feedback phases and record noise) = 1 (5 s.e.)",
              abs(complex(cd["u_mean_re"], cd["u_mean_im"]) - 1), 0, atol=5 * cd["u_sem"])
nn_ = np.arange(1, 10**5, dtype=float)
extra_inf = 2 * np.sum((2 * DELTA**2 / (nn_ * (nn_**2 - DELTA**2))) ** 2) / (32 * KAP * LAM)
check("record noise adds sum_i J_ij^2 / (32 kappa) to the decay rate: bulk value / lambda (infinite-chain sum), invisible here",
      G1["b"]["feedback_extra_rate_over_lambda_bulk"], extra_inf, rtol=1e-6)
Pmean = impulse.mean(axis=1)
Psd = impulse.std(axis=1, ddof=1) / math.sqrt(NTRAJ)
tstat = (Pmean - TB * FN) / Psd
t2 = float(np.mean(tstat**2))
G1["b"]["force"] = {"mean_t2": t2, "expected_t2": (NTRAJ - 1) / (NTRAJ - 3), "max_abs_t": float(np.abs(tstat).max()),
                    "edge_mass_impulse_mean": Pmean[0], "edge_mass_newton_impulse": TB * FN[0],
                    "edge_mass_impulse_sem": Psd[0], "per_trajectory_total_impulse_sd": float(impulse.sum(axis=0).std(ddof=1)),
                    "per_trajectory_total_impulse_mean": float(impulse.sum(axis=0).mean())}
check(f"mean impulse = T x Newtonian sum for all 4000 masses: mean t^2 over masses (Student t, 15 dof: {(NTRAJ - 1) / (NTRAJ - 3):.3f})",
      t2, (NTRAJ - 1) / (NTRAJ - 3), rtol=0.25)
check("end mass (largest Newtonian force): mean impulse / (T F_Newton)", Pmean[0] / (TB * FN[0]), 1.0, atol=5 * Psd[0] / abs(TB * FN[0]))
Ptot = impulse.sum(axis=0)
check_true(f"per trajectory the total momentum is not conserved (sd of sum_j P_j = {Ptot.std(ddof=1):.3g} against "
           f"T sum_j |F_j| = {TB * np.abs(FN).sum():.3g}); on average it is (mean {Ptot.mean():.3g}, within 5 s.e.)",
           Ptot.std(ddof=1) > 1e-3 * TB * np.abs(FN).sum() and abs(Ptot.mean()) < 5 * Ptot.std(ddof=1) / math.sqrt(NTRAJ))
l2z = [cp_data[x]["log2Z_mean"] for x in (1, 2, 3, 4)]
check_true(f"X-basis output per trajectory is a product distribution; log2 Z = sum_j log2(1 + X_j^2) falls from 4000 (t = 0) through "
           f"{', '.join(f'{v:.0f}' for v in l2z)} at t = 1..4/lambda towards 0 (uniform), never near Porter-Thomas (log2 Z = 1)",
           bool(np.all(np.diff(l2z) < 0) and l2z[0] < 4000 and l2z[-1] > 1))
# product form of Z checked by enumeration at N = 10 on one trajectory's product state
r10 = np.random.default_rng(10)
th = r10.uniform(0, np.pi, 10)
ph = r10.uniform(0, 2 * np.pi, 10)
st10 = np.array([1.0 + 0j])
for a, b in zip(th, ph):
    st10 = np.kron(st10, np.array([math.cos(a / 2), math.sin(a / 2) * np.exp(1j * b)]))
pz = np.abs(fwht(st10)) ** 2
Xs = np.sin(th) * np.cos(ph)
check("N = 10 product state: 2^N sum_x p(x)^2 by enumeration = prod_j (1 + X_j^2)", 2**10 * np.sum(pz**2), np.prod(1 + Xs**2), rtol=1e-10)
del Bmat, Bs, impulse, JW, W, JdW, B0dW, B1dW, dWb, flat

# quantum side at the same scale: exact nearest-neighbour two-body marginals of the coherent-field state, N = 4000 (no statevector)
t1 = time.perf_counter()
ngall = negativity(pair_rho_exact(hB, JB, TAU_PK, [(i, i + 1) for i in range(NB - 1)]))
t_all = time.perf_counter() - t1
spairs = [(0, 1), (1, 2), (2, 3), (999, 1000), (1999, 2000), (2000, 2001), (2999, 3000), (NB - 2, NB - 1), (1999, 2001), (1999, 2002)]
tau_scan = np.geomspace(0.05, 300.0, 36)
scan = np.array([negativity(pair_rho_exact(hB, JB, tau, spairs)) for tau in tau_scan])
iso = 0.5 * np.abs(np.sin(g1 * tau_scan / 2))
bulk = scan[:, 4]
death = tau_scan[np.argmax((bulk < 1e-12) & (tau_scan > 1))]
G1["a"]["N4000_pairs"] = {"all_nn_at_tau_1.3": {"min": ngall.min(), "median": float(np.median(ngall)), "max": ngall.max(),
                                                 "seconds": t_all},
                          "scan_pairs": spairs, "tau": tau_scan, "t_seconds": tau_scan / omega0, "negativity": scan,
                          "isolated_pair": iso, "bulk_nn_peak": bulk.max(), "bulk_nn_peak_tau": tau_scan[bulk.argmax()],
                          "bulk_nn_first_zero_tau_after_1": death,
                          "last_tau_any_scanned_pair_entangled": tau_scan[np.nonzero(scan.max(axis=1) > 1e-12)[0].max()]}
print(f"     coherent field, N = 4000 (exact two-body formula, all 3999 neighbour pairs in {t_all:.1f} s): negativity at tau = 1.3 "
      f"min {ngall.min():.4f}, median {np.median(ngall):.4f}; bulk peak {bulk.max():.4f} at tau = {tau_scan[bulk.argmax()]:.2f}; "
      f"bulk pair first separable at tau = {death:.2f}", flush=True)
check_true(f"coherent field, N = 4000: every nearest-neighbour pair is entangled at tau = 1.3 (t = 9 s; min negativity {ngall.min():.4f})",
           ngall.min() > 0.1)
check_true(f"coherent field, N = 4000: no scanned pair is entangled beyond tau = 30 (t = 3.6 min) while an isolated pair keeps oscillating "
           f"to 1/2 (max {iso[tau_scan > 30].max():.3f}): pairwise entanglement in the chain dies of monogamy",
           scan[tau_scan > 30].max() < 1e-12 and iso[tau_scan > 30].max() > 0.4)
del hB, JB

# small N: the averaged frame dynamics is the feedback master equation (Wiseman-Milburn), closed form because every operator is diagonal:
# rho_ss'(t) = rho_ss'(0) exp(t [i (Omega(s) - Omega(s')) - sum_k kappa_k (1 - z_k z'_k) - 1/2 sum_i (F_i(s) - F_i(s'))^2]),
# F_i(s) = sum_j J_ij s_j / (4 sqrt kappa_i): the quantum commutator is reproduced, plus dephasing; it must stay separable for every kappa
def frame_me(N, t, kap, E, J):
    s = bits(N)
    z = 1 - 2 * s
    F = (s @ J) / (4 * np.sqrt(kap))
    dec = kap * np.sum(1 - z[:, None, :] * z[None, :, :], axis=2) + 0.5 * np.sum((F[:, None, :] - F[None, :, :]) ** 2, axis=2)
    return np.exp(1j * t * (E[:, None] - E[None, :]) - t * dec) / 2**N


sep = {}
for N in (4, 6):
    h, J = chain_couplings(N)
    E = energy_table(h, J)
    kopt = math.sqrt(np.max((J**2).sum(axis=1))) / 8
    worst_pair, worst_cut, q_neg = 0.0, 0.0, 0.0
    cuts = [[q for q in range(N) if (mask >> q) & 1] for mask in range(1, 2 ** (N - 1))]
    for ks in np.geomspace(1e-3, 1e3, 13):
        for t in np.geomspace(1e-2, 50, 25):
            rho = frame_me(N, t, ks * kopt, E, J)
            worst_cut = max(worst_cut, max(-pt_min_subset(rho, N, cu) for cu in cuts))
            worst_pair = max(worst_pair, max(negativity(reduce_state(rho, N, [i, j])[None])[0]
                                             for i in range(N) for j in range(i + 1, N)))
    for t in np.geomspace(1e-2, 50, 25):
        psi = np.exp(1j * t * E) * 2 ** (-N / 2)
        q_neg = max(q_neg, -min(pt_min_subset(np.outer(psi, psi.conj()), N, cu) for cu in cuts))
    sep[N] = {"kappa_opt": kopt, "max_pair_negativity_frame": worst_pair, "max_bipartition_PT_negativity_frame": worst_cut,
              "max_bipartition_PT_negativity_quantum": q_neg}
    check(f"N = {N}: frame (feedback) state, 13 strengths kappa/kappa_opt = 1e-3..1e3 x 25 times: largest PT negativity over all "
          f"{len(cuts)} cuts", worst_cut, 0, atol=1e-12)
    check(f"N = {N}: frame state, largest pairwise negativity", worst_pair, 0, atol=1e-12)
    check_true(f"N = {N}: the coherent field entangles the same masses (largest PT eigenvalue magnitude {q_neg:.3f})", q_neg > 0.1)
G1["b"]["small_N_separability"] = sep

# Monte Carlo of the stochastic frame against the master equation, N = 4, kappa comparable to J (stringent), at t1
N4, kap4, t4 = 4, 0.2, 1.5
h4, J4 = chain_couplings(N4)
E4 = energy_table(h4, J4)
rme = frame_me(N4, t4, kap4, E4, J4)
r4 = np.random.default_rng(44)
n4 = 40000
z4 = r4.choice([1.0, -1.0], size=(n4, N4))
s4 = (1 - z4) / 2
W4 = r4.normal(0, math.sqrt(t4), size=(n4, N4))
Y4 = 2 * math.sqrt(kap4) * z4 * t4 + W4
q14 = 0.5 * (1 - np.tanh(2 * math.sqrt(kap4) * Y4))
c4 = 0.5 * sech(2 * math.sqrt(kap4) * Y4) * np.exp(-1j * ((h4 + s4 @ J4) * t4 - (W4 @ J4) / (4 * math.sqrt(kap4))))
single = np.empty((n4, N4, 2, 2), complex)
single[:, :, 0, 0], single[:, :, 1, 1], single[:, :, 0, 1], single[:, :, 1, 0] = 1 - q14, q14, c4, np.conj(c4)
joint = single[:, 0]
for q in range(1, N4):
    joint = np.einsum("tab,tcd->tacbd", joint, single[:, q]).reshape(n4, 2 ** (q + 1), 2 ** (q + 1))
zsc = np.abs(joint.mean(axis=0) - rme) / (np.maximum(joint.real.std(axis=0), joint.imag.std(axis=0)) / math.sqrt(n4) + 1e-15)
check("N = 4, kappa = 0.2 omega0, t = 1.5/omega0: 40000 exact trajectories (mixtures of product states) average to the master-equation "
      "state, largest |z| over 256 elements", zsc.max(), 0, atol=5.0)
# the same with a plain Euler integration of the joint 2^N stochastic Schroedinger equation (no product ansatz)
r5 = np.random.default_rng(45)
n5, dt5 = 8000, 0.005
sb = bits(N4)
zb = 1 - 2 * sb
psi5 = np.full((n5, 2**N4), 2 ** (-N4 / 2), complex)
sk4 = math.sqrt(kap4)
for _ in range(int(round(t4 / dt5))):
    pr = np.abs(psi5) ** 2
    Zexp = pr @ zb
    dY = 2 * sk4 * Zexp * dt5 + r5.normal(0, math.sqrt(dt5), size=(n5, N4))
    shat = 0.5 * (dt5 - dY / (2 * sk4))                     # s_hat_i dt
    psi5 = psi5 * np.exp(sk4 * dY @ zb.T - kap4 * N4 * dt5)  # measurement (exact linear factor for a step)
    psi5 = psi5 * np.exp(1j * (sb @ (h4 * dt5) + np.einsum("tj,sj->ts", shat @ J4, sb)))   # feedback field of the records
    psi5 /= np.linalg.norm(psi5, axis=1, keepdims=True)
schmidt = 0.0
for cut in range(1, N4):
    sv = np.linalg.svd(psi5[:200].reshape(200, 2**cut, -1), compute_uv=False)
    schmidt = max(schmidt, float((sv[:, 1] / sv[:, 0]).max()))
r5m = np.einsum("ts,tu->su", psi5, psi5.conj()) / n5
check("joint 2^4 stochastic Schroedinger equation (Euler, 8000 trajectories): every trajectory stays a product, max s2/s1 over cuts",
      schmidt, 0, atol=1e-12)
check("joint SSE average = master equation (max |difference| over 256 elements; statistical + O(dt) tolerance 0.02)",
      np.abs(r5m - rme).max(), 0, atol=0.02)
G1["b"]["mc_vs_master_equation"] = {"max_z_exact_traj": zsc.max(), "joint_sse_max_abs_diff": np.abs(r5m - rme).max(),
                                    "joint_sse_max_schmidt_ratio": schmidt}

# cost: measured 2^N statevector against the frame, extrapolated
Ns = np.array([N for N in NS if N >= 16])
ts_ = np.array([timing[N]["state_plus_Z_s_median"] + timing[N]["table_s"] for N in Ns])
b_fit, a_fit = np.polyfit(Ns, np.log2(ts_), 1)
log10_t4000 = (a_fit + b_fit * 4000) * math.log10(2)
log10_t4000_pure = math.log10(ts_[-1]) + (4000 - Ns[-1]) * math.log10(2)    # conservative: exactly 2x per added mass from N = 24
G1["cost"] = {"statevector_seconds": timing, "fit_log2_seconds_vs_N": {"slope": b_fit, "intercept": a_fit},
              "statevector_bytes_N24": 16 * 2**24, "log10_statevector_bytes_N4000": math.log10(16) + 4000 * math.log10(2),
              "log10_seconds_statevector_N4000_extrapolated_fit": log10_t4000,
              "log10_seconds_statevector_N4000_pure_2N_from_N24": log10_t4000_pure,
              "seconds_statevector_N24_table_state_Z": ts_[-1],
              "frame_N4000_seconds": t_loop, "frame_N4000_seconds_per_step_per_trajectory": t_loop / (NSTEP * NTRAJ),
              "frame_memory_bytes_N4000": 3 * 8 * NB * NB}
print(f"     cost: statevector time ~ 2^({b_fit:.2f} N); N = 24 table + state + Z {ts_[-1]:.2f} s; extrapolated N = 4000: at least "
      f"10^{log10_t4000_pure:.0f} s (pure 2^N), 10^{log10_t4000:.0f} s (fit); frame N = 4000: {t_loop:.1f} s for {NSTEP * NTRAJ} "
      f"trajectory-steps", flush=True)
check("statevector cost grows as 2^N: fitted exponent of 2 per added mass (N = 16..24)", b_fit, 1.0, atol=0.35)

# =================================================================================================================================
print("\n[G2] Bose-Marletto-Vedral under (Q) quantum gravity, (Q+DP) plus Diosi-Penrose decoherence, (G) GUID frame plus DP")
G2 = RES["G2"] = {}


def EG_sphere(b):
    """Diosi-Penrose self-energy of the difference of a uniform sphere and its copy displaced by b (units G M^2 / R, R = 1):
    2 l^2 - 3/2 l^3 + 1/5 l^5 for l = b/2R <= 1, 6/5 - R/b beyond (Howl, Penrose, Fuentes 2019, Eq. 23)."""
    b = np.asarray(b, float)
    lam_ = b / 2
    with np.errstate(divide="ignore"):
        return np.where(lam_ <= 1, 2 * lam_**2 - 1.5 * lam_**3 + 0.2 * lam_**5, 1.2 - 1 / np.where(b > 0, b, 1))


def mutual_sphere(b):
    """G int int rho1 rho2 / |x - y| for two uniform unit spheres (G = M = R = 1), centres b apart, by radial quadrature."""
    phi = lambda r: 1 / r if r >= 1 else (3 - r * r) / 2

    def area(r):
        if b == 0:
            return 4 * math.pi * r * r if r <= 1 else 0.0
        if r <= 1 - b:
            return 4 * math.pi * r * r
        if r >= b + 1 or r <= b - 1:
            return 0.0
        return math.pi * r / b * (1 - (r - b) ** 2)

    pts = sorted({0.0, max(0.0, 1 - b), abs(b - 1), 1.0, b + 1})
    tot = sum(integrate.quad(lambda r: phi(r) * area(r), pts[k], pts[k + 1], epsabs=1e-14, epsrel=1e-12)[0]
              for k in range(len(pts) - 1) if pts[k + 1] > pts[k])
    return tot * 3 / (4 * math.pi)


check("self-energy integral of a uniform sphere: G int int rho rho / |x-y| = 6/5 G M^2 / R (quadrature)", mutual_sphere(0.0), 1.2, rtol=1e-9)
devs = [abs((1.2 - mutual_sphere(b)) - float(EG_sphere(b))) for b in (0.2, 1.0, 1.9, 2.0, 3.0, 10.0, 2 * dx_b / (2 * R_b))]
check("E_G of displaced spheres: quadrature = closed form (overlap polynomial; 6/5 - R/b for b >= 2R, shell theorem), max abs diff",
      max(devs), 0, atol=1e-9)


def two_mass(xA, xB, m, R, rate="paper"):
    r = np.array([[np.linalg.norm(xA[a] - xB[b]) for b in (0, 1)] for a in (0, 1)])
    gm = G * m * m / hbar
    Om = gm / r
    Jab = Om[1, 1] - Om[1, 0] - Om[0, 1] + Om[0, 0]          # s-basis coupling: |Jab| = entangling phase rate
    if rate == "paper":
        GA = GB = gm / R
    else:
        GA = gm / R * float(EG_sphere(np.linalg.norm(xA[1] - xA[0]) / R))
        GB = gm / R * float(EG_sphere(np.linalg.norm(xB[1] - xB[0]) / R))
    cross = np.zeros((4, 4))
    for A, (a, b) in enumerate(S4):
        for B, (a2, b2) in enumerate(S4):
            if a != a2 and b != b2:
                cross[A, B] = gm * (1 / r[a, b] - 1 / r[a, b2] - 1 / r[a2, b] + 1 / r[a2, b2])
    return {"r": r, "Om": Om, "J": Jab, "omega": abs(Jab), "GA": GA, "GB": GB, "cross": cross}


HA = np.array([[abs(a - a2) for (a2, b2) in S4] for (a, b) in S4], float)
HB = np.array([[abs(b - b2) for (a2, b2) in S4] for (a, b) in S4], float)


def hyp_states(M, ts, kind, kap=None):
    ph = np.array([M["Om"][a, b] for (a, b) in S4])
    psi = 0.5 * np.exp(1j * ph[None, :] * ts[:, None])
    rho = psi[:, :, None] * psi[:, None, :].conj()
    if kind == "Q":
        dec = np.zeros((4, 4))
    elif kind == "Q+DP local":
        dec = M["GA"] * HA + M["GB"] * HB
    elif kind == "Q+DP full":
        dec = M["GA"] * HA + M["GB"] * HB + M["cross"]
    elif kind == "G":
        kA = kB = kap
        sA = np.array([a for (a, b) in S4], float)
        sB = np.array([b for (a, b) in S4], float)
        FA, FB = M["J"] * sB / (4 * math.sqrt(kA)), M["J"] * sA / (4 * math.sqrt(kB))
        dec = 2 * kA * HA + 2 * kB * HB + 0.5 * ((FA[:, None] - FA[None, :]) ** 2 + (FB[:, None] - FB[None, :]) ** 2)
    return rho * np.exp(-dec[None] * ts[:, None, None])


xA = np.array([[-d_b / 2 - dx_b / 2, 0, 0], [-d_b / 2 + dx_b / 2, 0, 0]])
xB = np.array([[d_b / 2 - dx_b / 2, 0, 0], [d_b / 2 + dx_b / 2, 0, 0]])
Mb = two_mass(xA, xB, m_b, R_b)
Mbx = two_mass(xA, xB, m_b, R_b, rate="exact")
rho_b = Mb["omega"] / lam_B
gfun = lambda d, dx: 2 * dx**2 / (d * (d - dx) * (d + dx))     # = 1/(d-dx) + 1/(d+dx) - 2/d without cancellation
check("BMV entangling phase rate omega = (G m^2/hbar)[1/(d-dx) + 1/(d+dx) - 2/d], rad/s", Mb["omega"], 0.1256, rtol=2e-3)
check("rho = omega / lambda_B = R [1/(d-dx) + 1/(d+dx) - 2/d] (identity)", rho_b, R_b * gfun(d_b, dx_b), rtol=1e-12)
check("rho for the Bose geometry (= entangling phase per coherence time, checks.py Q19: 1.74e-3 rad)", rho_b, 1.74e-3, rtol=1e-2)
rhos_m = [two_mass(xA, xB, mm, R_b)["omega"] / (G * mm * mm / (hbar * R_b)) for mm in (1e-18, 1e-14, 1e-10, 1.0)]
check("rho is independent of the mass at fixed geometry (m = 1e-18 .. 1 kg): relative spread", np.ptp(rhos_m) / rho_b, 0, atol=1e-12)
check("exact sphere DP rate for the Bose split, (G m^2/hbar)(6/5R - 1/dx), per s", Mbx["GA"], lam_B * (1.2 - R_b / dx_b), rtol=1e-12)
G2["bose_instance"] = {"omega_rad_s": Mb["omega"], "lambda_B_per_s": lam_B, "lambda_DP_exact_per_s": Mbx["GA"], "rho_paper": rho_b,
                       "rho_exact_DP": Mb["omega"] / Mbx["GA"], "coherence_time_ms": 1e3 / lam_B, "t_1rad_s": 1 / Mb["omega"],
                       "t_pi_s": math.pi / Mb["omega"]}

# supremum of rho over geometries (R = 1 units; spheres never overlap: every inter-mass branch distance >= 2R)
u2 = 2.0
dxs = np.geomspace(1e-4, 1e7, 400)
rho_col = gfun(u2 + dxs, dxs)                   # collinear (the task's formula), closest approach d - dx = 2R
rho_col_u = [gfun(u + 10.0, 10.0) for u in np.linspace(2, 50, 49)]
check_true("collinear: rho increases with dx at d - dx = 2R and decreases with the closest approach",
           bool(np.all(np.diff(rho_col) > 0) and np.all(np.diff(rho_col_u) < 0)))
check("collinear supremum: rho -> 1/2 (dx -> infinity, d - dx = 2R); value at dx = 1e7 R", rho_col[-1], 0.5, rtol=1e-6)
check_true("collinear: rho < 1/2 for every finite geometry (never attained)", bool(rho_col.max() < 0.5))
gap_um = 200.0   # closest approach of Bose et al. (Casimir-Polder at a tenth of gravity); rho_sup = R/u with a gap
check("collinear with Bose et al.'s Casimir gap d - dx >= 200 um: rho <= R/(d-dx) = 4.4e-3", R_b / (gap_um * 1e-6), 4.4e-3, rtol=1e-2)
par = 1 - 2 / np.sqrt(dxs**2 + 4)               # parallel splits side by side at 2R (touching branches): best two-sphere geometry
check("any two-sphere geometry: omega <= (G m^2/hbar)(1/r_00 + 1/r_11) <= lambda_B, sup rho = 1 (parallel splits, dx -> inf)", par[-1], 1.0,
      rtol=1e-6)
rngG = np.random.default_rng(22)
nG = 200000
dA = np.exp(rngG.uniform(np.log(1e-2), np.log(1e4), nG))
dB = np.exp(rngG.uniform(np.log(1e-2), np.log(1e4), nG))
uA = rngG.normal(size=(nG, 3))
uA /= np.linalg.norm(uA, axis=1, keepdims=True)
uB = rngG.normal(size=(nG, 3))
uB /= np.linalg.norm(uB, axis=1, keepdims=True)
cB = rngG.normal(size=(nG, 3)) * (2 + np.maximum(dA, dB))[:, None] * rngG.uniform(0.2, 1.5, (nG, 1))
A0, A1, B0, B1 = np.zeros((nG, 3)), uA * dA[:, None], cB, cB + uB * dB[:, None]
rr = np.stack([np.linalg.norm(A0 - B0, axis=1), np.linalg.norm(A0 - B1, axis=1), np.linalg.norm(A1 - B0, axis=1),
               np.linalg.norm(A1 - B1, axis=1)], axis=1)
ok = rr.min(axis=1) >= 2
om = np.abs(1 / rr[:, 0] + 1 / rr[:, 3] - 1 / rr[:, 1] - 1 / rr[:, 2])[ok]
cs_ratio = om / (2 * np.sqrt(EG_sphere(dA[ok]) * EG_sphere(dB[ok])))
ex_ratio = om / np.sqrt(EG_sphere(dA[ok]) * EG_sphere(dB[ok]))
check_true(f"{ok.sum()} random non-overlapping two-sphere geometries: rho (paper rate) <= 1, max {om.max():.4f}", bool(om.max() <= 1))
check_true(f"Cauchy-Schwarz on the positive Newton kernel: omega <= 2 sqrt(Gamma_A Gamma_B) with exact DP rates "
           f"(max omega / (2 sqrt(Gamma_A Gamma_B)) over samples {cs_ratio.max():.4f})", bool(cs_ratio.max() <= 1))
check("exact DP rates: sup omega / Gamma over sphere geometries -> 5/6 (parallel, dx -> inf); value at dx = 1e7 R",
      par[-1] / float(EG_sphere(dxs[-1])), 5 / 6, rtol=1e-6)
check_true(f"random geometries never exceed 5/6 with exact DP rates (max {ex_ratio.max():.4f})", bool(ex_ratio.max() <= 5 / 6))
check("collinear, exact DP rates: sup -> 1/2 again, now as dx -> 0 at d = 2R + dx; value at dx = 1e-4 R",
      gfun(2 + 1e-4, 1e-4) / float(EG_sphere(1e-4)), 0.5, rtol=1e-3)
G2["supremum"] = {"collinear_paper_rate": 0.5, "collinear_exact_DP": 0.5, "any_two_spheres_paper_rate": 1.0,
                  "any_two_spheres_exact_DP": 5 / 6, "random_geometries": int(ok.sum()), "random_max_paper": om.max(),
                  "random_max_exact": ex_ratio.max(), "random_max_cauchy_schwarz_ratio": cs_ratio.max(),
                  "collinear_with_200um_gap": R_b / (gap_um * 1e-6),
                  "collinear_scan": {"dx_over_R": dxs[::40], "rho_paper": rho_col[::40], "rho_exact": (rho_col / EG_sphere(dxs))[::40]}}

# entanglement threshold: Q with dephasing at lambda per mass and entangling rate omega; r = omega/lambda (units lambda = 1)
tsr = np.concatenate([[0.0], np.geomspace(1e-5, 40, 2500)])


def canon(r, corr=0.0):
    M = {"Om": np.array([[0.0, 0.0], [0.0, r]]), "J": r, "GA": 1.0, "GB": 1.0, "cross": np.zeros((4, 4))}
    if corr:
        M["cross"][0, 3] = M["cross"][3, 0] = -corr * r     # (00,11) decays at 2 lambda - omega, (01,10) at 2 lambda + omega
        M["cross"][1, 2] = M["cross"][2, 1] = corr * r
    return M


def maxneg(r, corr=0.0):
    return float(negativity(hyp_states(canon(r, corr), tsr, "Q+DP full" if corr else "Q+DP local")).max())


def bisect(fun, lo, hi, it=40):
    for _ in range(it):
        mid = 0.5 * (lo + hi)
        lo, hi = (lo, mid) if fun(mid) > 1e-13 else (mid, hi)
    return 0.5 * (lo + hi)


rc_loc = bisect(maxneg, 1.0, 3.0)
rc_full = bisect(lambda r: maxneg(r, 1.0), 1.0, 3.0)
rc_full_m = bisect(lambda r: maxneg(r, -1.0), 1.0, 3.0)
check("threshold: Q + independent dephasing lambda per mass is ever entangled iff omega/lambda > 2 (bisection over 40 s of evolution)",
      rc_loc, 2.0, rtol=1e-4)
small = hyp_states(canon(3.0), np.array([1e-7]), "Q+DP local")
check("first order: smallest PT eigenvalue ~ (t/4)(2 lambda - omega) (omega = 3 lambda, t = 1e-7)", neg_pt_min(small)[0] / 1e-7, -0.25,
      rtol=1e-4)
check("threshold with the full DP kernel (correlated inter-mass term, locked to omega): omega/Gamma > sqrt 2", rc_full, math.sqrt(2),
      rtol=1e-4)
check("same with the opposite sign of the correlation", rc_full_m, math.sqrt(2), rtol=1e-4)
G2["threshold"] = {"local_dephasing": rc_loc, "full_DP_kernel": rc_full, "LOCC_sufficient_local": 2.0, "KTM_qubit_min_decoherence": "omega/2",
                   "margin_local_vs_sup_paper": rc_loc / 1.0, "margin_full_vs_sup_exact": rc_full / (5 / 6)}

# the instance: time series under the hypotheses (seconds)
tphys = np.concatenate([[0.0], np.geomspace(1e-6, 40.0, 3000)])
kap_B = lam_B / 2                                    # balance rule, Bridge B: measurement dephasing 2 kappa = lambda_B
kap_K = Mb["omega"] / 8                              # Kafri-Taylor-Milburn optimum for qubits (total decoherence omega/2)
series = {"Q": hyp_states(Mb, tphys, "Q"), "Q+DP local": hyp_states(Mb, tphys, "Q+DP local"),
          "Q+DP exact local": hyp_states(Mbx, tphys, "Q+DP local"), "Q+DP full": hyp_states(Mbx, tphys, "Q+DP full"),
          "G": hyp_states(Mb, tphys, "G", kap_B), "G at KTM minimum": hyp_states(Mb, tphys, "G", kap_K)}
Mt = dict(Mb)
Mt["GA"] = Mt["GB"] = 0.99 * Mb["omega"] / 2
series["Q + dephasing 0.99 omega/2"] = hyp_states(Mt, tphys, "Q+DP local")
# witnesses in the local frame of the coherent-field prediction
u_ = (Mb["Om"][1, 0] - Mb["Om"][0, 0]) * tphys
v_ = (Mb["Om"][0, 1] - Mb["Om"][0, 0]) * tphys
Xp = np.array([[0, 1], [1, 0]], complex)
Zp = np.diag([1.0, -1.0]).astype(complex)
Wst = np.kron(Xp, Zp) + np.kron(Zp, Xp)
loc = np.zeros((tphys.size, 4), complex)
for A, (a, b) in enumerate(S4):
    loc[:, A] = np.exp(-1j * (u_ * a + v_ * b))
ptQ = series["Q"].reshape(-1, 2, 2, 2, 2).swapaxes(-1, -3).reshape(-1, 4, 4)
ev, evec = np.linalg.eigh(ptQ)
eopt = evec[:, :, 0]
wit = {}
for k, rho in series.items():
    rl = loc[:, :, None] * rho * loc[:, None, :].conj()
    ws = np.einsum("tab,ba->t", rl, Wst).real
    pt = rho.reshape(-1, 2, 2, 2, 2).swapaxes(-1, -3).reshape(-1, 4, 4)
    wo = np.einsum("ta,tab,tb->t", eopt.conj(), pt, eopt).real
    ng = negativity(rho)
    wit[k] = {"max_negativity": ng.max(), "t_at_max_s": tphys[ng.argmax()], "max_stabiliser_witness": ws.max(),
              "min_optimal_witness": wo.min(), "negativity_at_t_pi": float(np.interp(math.pi / Mb["omega"], tphys, ng))}
G2["hypotheses"] = wit
G2["series_sampled"] = {"t_s": tphys[::150], **{k: negativity(v)[::150] for k, v in series.items()}}
check("(Q) negativity at the entangling phase pi (t = 25 s) is maximal, 1/2", wit["Q"]["negativity_at_t_pi"], 0.5, rtol=1e-3)
check("(Q) stabiliser witness <X Z> + <Z X> (separable bound 1) reaches 2 = 1 - cos(pi)", wit["Q"]["max_stabiliser_witness"], 2.0, rtol=1e-3)
for k in ("Q+DP local", "Q+DP exact local", "Q+DP full", "G", "G at KTM minimum"):
    check(f"({k}) largest negativity over 0..40 s", wit[k]["max_negativity"], 0, atol=1e-14)
    check_true(f"({k}) stabiliser witness never above 1 (max {wit[k]['max_stabiliser_witness']:.2e}); optimal PPT witness never "
               f"negative (min {wit[k]['min_optimal_witness']:.1e})",
               wit[k]["max_stabiliser_witness"] < 1 and wit[k]["min_optimal_witness"] > -1e-14)
check_true(f"control: Q with dephasing at 0.99 x omega/2 does entangle (max negativity {wit['Q + dephasing 0.99 omega/2']['max_negativity']:.2e})",
           wit["Q + dephasing 0.99 omega/2"]["max_negativity"] > 1e-6)


# Bose et al.'s spin witness as printed in the accepted manuscript, and a valid variant: maxima over product states
def prodmax(Wop):
    """Largest |<W>| over product pure states (Nelder-Mead from 40 seeded starts)."""
    def ket(t, p):
        return np.array([math.cos(t / 2), math.sin(t / 2) * np.exp(1j * p)])

    def f(x):
        v = np.kron(ket(x[0], x[1]), ket(x[2], x[3]))
        return -abs(np.vdot(v, Wop @ v).real)

    rs = np.random.default_rng(7)
    return max(-optimize.minimize(f, rs.uniform(0, np.pi, 4) * np.array([1, 2, 1, 2]), method="Nelder-Mead",
                                  options=dict(xatol=1e-10, fatol=1e-13, maxiter=4000)).fun for _ in range(40))


Yp = np.array([[0, -1j], [1j, 0]])
w_print = prodmax(np.kron(Xp, Zp) - np.kron(Yp, Zp))
w_alt = prodmax(np.kron(Xp, Zp) + np.kron(Yp, Yp))
check("Bose et al. witness as printed, |<sx sz> - <sy sz>|: maximum over product states (so a bound of 1 does not certify)", w_print,
      math.sqrt(2), rtol=1e-6)
check("variant |<sx sz> + <sy sy>|: maximum over product states is 1 (a valid bound)", w_alt, 1.0, rtol=1e-6)
G2["bose_witness_product_max"] = {"as_printed": w_print, "variant_xz_plus_yy": w_alt}

# =================================================================================================================================
print("\n[G3] Classical-quantum dynamics: qubit (sigma_z) and a classical momentum p; positivity and the balance rule")
G3 = RES["G3"] = {}
D0, D2, s0 = 1.0, 1.0, 0.1
Pmax, hp = 22.0, 0.01
pg = np.arange(-Pmax, Pmax + hp / 2, hp)
npg = pg.size
Id = sparse.identity(npg, format="csr")
d1 = sparse.diags([-1.0, 1.0], [-1, 1], shape=(npg, npg)) / (2 * hp)
d2 = sparse.diags([1.0, -2.0, 1.0], [-1, 0, 1], shape=(npg, npg)) / hp**2
T3, nt3 = 3.0, 61
ts3 = np.linspace(0, T3, nt3)
gauss0 = np.exp(-pg**2 / (2 * s0**2)) / math.sqrt(2 * math.pi * s0**2)


def cq_blocks_exact(D1, D2_, ts, s0_=s0, pp=pg):
    """Exact blocks rho_00, rho_11, rho_01 of the toy from a Gaussian of width s0 times |+><+|."""
    s2 = s0_**2 + D2_ * ts[:, None]
    nrm = 1 / np.sqrt(2 * math.pi * s2)
    A = 0.5 * nrm * np.exp(-(pp - D1 * ts[:, None]) ** 2 / (2 * s2))
    B = 0.5 * nrm * np.exp(-(pp + D1 * ts[:, None]) ** 2 / (2 * s2))
    C = 0.5 * nrm * np.exp(-2 * D0 * ts[:, None]) * np.exp(-pp**2 / (2 * s2))
    return A, B, C


cq = {}
for r in (0.5, 1.0, 1.01, 2.0):
    D1 = 2 * math.sqrt(r * D0 * D2)
    # d rho/dt = D0 (Z rho Z - rho) - (D1/2) d/dp {Z, rho} + (D2/2) d^2/dp^2 rho, blockwise: rho_00 drifts at +D1, rho_11 at -D1,
    # rho_01 does not drift and decays at 2 D0
    a = expm_multiply((-D1 * d1 + 0.5 * D2 * d2).tocsr(), 0.5 * gauss0, start=0, stop=T3, num=nt3, endpoint=True)
    b = expm_multiply((D1 * d1 + 0.5 * D2 * d2).tocsr(), 0.5 * gauss0, start=0, stop=T3, num=nt3, endpoint=True)
    c = expm_multiply((-2 * D0 * Id + 0.5 * D2 * d2).tocsr(), 0.5 * gauss0, start=0, stop=T3, num=nt3, endpoint=True)
    lmin = (a + b) / 2 - np.sqrt(((a - b) / 2) ** 2 + c**2)
    peak = (a + b).max(axis=1)
    rel = lmin.min(axis=1) / peak
    A, B, C = cq_blocks_exact(D1, D2, ts3)
    err = max(np.abs(a - A).max(), np.abs(b - B).max(), np.abs(c - C).max()) / A.max()
    tstar = 4 * D0 * s0**2 / (D1**2 - 4 * D0 * D2) if r > 1 else float("inf")
    first = ts3[np.argmax(rel < -1e-9)] if (rel < -1e-9).any() else None
    cq[r] = {"D1": D1, "ratio_D1sq_over_4D0D2": r, "fd_max_rel_error": err, "min_rel_block_eigenvalue": rel.min(),
             "joint_object_min_eigenvalue": hp * lmin.min(), "joint_negative_mass_at_T": -hp * np.clip(lmin[-1], None, 0).sum(),
             "first_negative_time": first, "t_star_theory": tstar, "rel_min_eig_series": rel[::6]}
    print(f"     D1^2/(4 D0 D2) = {r}: min block eigenvalue / peak {rel.min():.3e}, first negative t = {first}, theory t* = {tstar:.3g}",
          flush=True)
G3["fd_runs"] = cq
G3["normalisation"] = {"this_toy": "d rho/dt = D0 (Z rho Z - rho) - (D1/2) d_p {Z, rho} + (D2/2) d_p^2 rho",
                       "OSSWD_Eq9": "first moment D1^{0a} = D1/2, second moment D2^{00} = D2/2 (their D_n carry 1/n!)",
                       "OSSWD_Eq23": "(D1/2)^2 / D0 <= 2 (D2/2)  <=>  D1^2 <= 4 D0 D2", "grid": {"P": Pmax, "h": hp, "points": npg},
                       "s0": s0, "D0": D0, "D2": D2, "T": T3}
check("finite-difference evolution matches the exact Gaussian solution (max error / peak over all runs)", max(v["fd_max_rel_error"] for v in cq.values()),
      0, atol=5e-4)
check("D1^2 = 2 D0 D2 (inside the bound): smallest block eigenvalue / peak", cq[0.5]["min_rel_block_eigenvalue"], 0, atol=1e-12)
check("D1^2 = 4 D0 D2 (balance rule, equality): smallest block eigenvalue / peak", cq[1.0]["min_rel_block_eigenvalue"], 0, atol=1e-12)
check("D1^2 = 4.04 D0 D2 (1% beyond): positivity fails first at t* = 4 D0 s0^2 / (D1^2 - 4 D0 D2) = 1.00", cq[1.01]["first_negative_time"],
      1.0, atol=T3 / (nt3 - 1) + 1e-9)
check_true(f"D1^2 = 8 D0 D2: the joint classical-quantum object has negative eigenvalues (min block eigenvalue / peak "
           f"{cq[2.0]['min_rel_block_eigenvalue']:.3f}, negative mass {cq[2.0]['joint_negative_mass_at_T']:.2e})",
           cq[2.0]["min_rel_block_eigenvalue"] < -0.1)
check("mapping: at equality OSSWD's (D1/2)^2/D0 equals 2 (D2/2)", (1.0) ** 2 / D0, 2 * (D2 / 2), rtol=1e-12)
# minimal diffusion for given decoherence and back-reaction: D2_min(T) from the blocks, against D1^2/(4 D0) - s0^2/T
D1f, Tlong = 2.0, 50.0
tgrid = np.linspace(0, Tlong, 2001)


def positive_until(D2_):
    A, B, C = cq_blocks_exact(D1f, D2_, tgrid[1:], pp=np.linspace(-3, 3, 41))
    return bool(((A * B - C * C) >= -1e-14 * (A + B) ** 2).all())


lo, hi = 0.5, 1.5
for _ in range(50):
    mid = 0.5 * (lo + hi)
    lo, hi = (lo, mid) if positive_until(mid) else (mid, hi)
check("smallest diffusion keeping positivity up to T = 50: D1^2/(4 D0) - s0^2/T -> the balance-rule value as T grows", hi,
      D1f**2 / (4 * D0) - s0**2 / Tlong, rtol=1e-4)
# the equality case is the measurement-and-feedback unravelling: p = alpha Y (the record), D1 = 2 alpha sqrt(D0), D2 = alpha^2
r6 = np.random.default_rng(66)
n6, t6 = 400000, 1.0
alpha = 1.0
z6 = r6.choice([1.0, -1.0], size=n6)
Y6 = 2 * math.sqrt(D0) * z6 * t6 + r6.normal(0, math.sqrt(t6), n6)
q0 = 0.5 * (1 + np.tanh(2 * math.sqrt(D0) * Y6))
c6 = 0.5 * sech(2 * math.sqrt(D0) * Y6)
pur = {}
for lab, beta in (("equality", 0.0), ("2x diffusion", 1.0)):
    p6 = alpha * Y6 + beta * r6.normal(0, math.sqrt(t6), n6)
    edges = np.linspace(-1.025, 1.025, 42)          # 41 bins of width 0.05 centred on -1.00 .. 1.00
    k6 = np.digitize(p6, edges) - 1
    inb = (k6 >= 0) & (k6 < edges.size - 1)
    sA = np.bincount(k6[inb], q0[inb], edges.size - 1)
    sB = np.bincount(k6[inb], (1 - q0)[inb], edges.size - 1)
    sC = np.bincount(k6[inb], c6[inb], edges.size - 1)
    mix = 4 * (sA * sB - sC**2) / (sA + sB) ** 2
    pur[lab] = {"bins_p": 0.5 * (edges[1:] + edges[:-1]), "mixedness_4det_over_tr2": mix, "max_mixedness": mix.max(),
                "mixedness_at_p0": mix[20]}
G3["unravelling"] = {"n_traj": n6, "t": t6, "D1": 2 * alpha * math.sqrt(D0), "D2_equality": alpha**2, **pur}
check("unravelling: mean coherence int rho_01 dp = exp(-2 D0 t)/2", c6.mean(), 0.5 * math.exp(-2 * D0 * t6), rtol=5 * c6.std() / c6.mean() / math.sqrt(n6))
check("unravelling: branch-0 mean momentum = D1 t", np.sum(q0 * alpha * Y6) / np.sum(q0), 2 * alpha * math.sqrt(D0) * t6, rtol=0.01)
check_true(f"at equality p is a perfect record: every block rho(p) is pure (largest 4 det/tr^2 over |p| < 1 is "
           f"{pur['equality']['max_mixedness']:.1e}, bin-width limited)", pur["equality"]["max_mixedness"] < 2e-3)
check("above equality (D2 doubled) blocks are mixed: 4 det/tr^2 at p = 0 equals 1 - exp(-(4 D0 D2 - D1^2) t / D2) = 1 - e^-2",
      pur["2x diffusion"]["mixedness_at_p0"], 1 - math.exp(-2.0), rtol=0.03)

# =================================================================================================================================
print("\n[G4] Two gravitationally coupled oscillators: quantum coupling against the Kafri-Taylor-Milburn classical channel")
G4 = RES["G4"] = {}
Kc = 0.1                                       # units hbar = m = Omega = 1; H = sum (p^2 + x^2)/2 - K x1 x2
Amat = np.array([[0, 1, 0, 0], [-1, 0, Kc, 0], [0, 0, 0, 1], [Kc, 0, -1, 0]], float)
A0m = np.array([[0, 1, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 1], [0, 0, -1, 0]], float)
Omg = np.kron(np.eye(2), np.array([[0, 1], [-1, 0]]))
Ppt = np.diag([1, 1, 1, -1.0])


def lyap_series(sig0, A, D, ts):
    n = 4
    L = np.kron(np.eye(n), A) + np.kron(A, np.eye(n))
    M = np.zeros((n * n + 1, n * n + 1))
    M[: n * n, : n * n] = L
    M[: n * n, -1] = D.reshape(-1)
    E = expm(M * (ts[1] - ts[0]))
    v = np.concatenate([sig0.reshape(-1), [1.0]])
    out = np.empty((ts.size, 4, 4))
    for k in range(ts.size):
        out[k] = v[:-1].reshape(4, 4)
        v = E @ v
    return out


def two_nu(sig):
    st = Ppt @ sig @ Ppt
    return 2 * np.abs(np.linalg.eigvals(1j * Omg @ st)).min()


ts4 = np.linspace(0, 200, 4001)
vac = np.eye(4) / 2
sq = np.diag([math.exp(-2), math.exp(2), math.exp(-2), math.exp(2)]) / 2
Dk = lambda k: k + Kc**2 / (4 * k)
res4 = {}
for name, s_in in (("vacuum", vac), ("squeezed r=1", sq)):
    q = lyap_series(s_in, Amat, np.zeros((4, 4)), ts4)
    tn = np.array([two_nu(s) for s in q])
    res4[name] = {"Q_max_log_neg": max(0.0, -np.log2(tn.min())), "Q_t_at_max": ts4[tn.argmin()]}
    worst = np.inf
    for k in np.geomspace(1e-2, 1e2, 9) * Kc / 2:
        sgm = lyap_series(s_in, Amat, np.diag([0, Dk(k), 0, Dk(k)]), ts4[::4])
        worst = min(worst, min(two_nu(s) for s in sgm))
    res4[name]["KTM_min_2nu_all_k"] = worst
    under = lyap_series(s_in, Amat, np.diag([0, 0.99 * Kc, 0, 0.99 * Kc]), ts4[:400])
    res4[name]["below_minimum_0.99K_max_log_neg"] = max(0.0, -np.log2(min(two_nu(s) for s in under)))
    check_true(f"{name}: quantum coupling entangles (max log-negativity {res4[name]['Q_max_log_neg']:.3f})", res4[name]["Q_max_log_neg"] > 0.01)
    check(f"{name}: KTM channel, 9 strengths k = (1e-2..1e2) K/2, t <= 200: smallest 2 nu (>= 1 means log-negativity exactly 0)", min(worst, 1.0),
          1.0, atol=1e-9)
G4["log_negativity"] = res4
check_true(f"vacuum: quantum coupling plus dephasing at 0.99 K (just below the channel's minimum) entangles (log-neg "
           f"{res4['vacuum']['below_minimum_0.99K_max_log_neg']:.2e}): the KTM minimum is the separability edge",
           res4["vacuum"]["below_minimum_0.99K_max_log_neg"] > 1e-5)
kopt = optimize.minimize_scalar(Dk, bounds=(1e-4, 10), method="bounded", options=dict(xatol=1e-12)).x
check("heating D(k) = k + K^2/(4k) is minimal at k = K/2 (KTM Eq. 15: Gamma = K/2)", kopt, Kc / 2, rtol=1e-6)
check("minimal momentum diffusion = hbar K (KTM Eq. 19)", Dk(kopt), Kc, rtol=1e-9)
G4["heating_vs_k"] = {"k_over_K": np.geomspace(1e-2, 1e2, 9) / 2, "D_over_K": [Dk(k) / Kc for k in np.geomspace(1e-2, 1e2, 9) * Kc / 2],
                      "k_opt": kopt, "D_min": Dk(kopt), "coherence_decay_rate": "D (x - x')^2 / (2 hbar^2) >= K (x - x')^2 / (2 hbar)"}
# conditional (per-trajectory) dynamics: local measurement + feedback; the conditional covariance never couples the masses
r7 = np.random.default_rng(77)
n7, dt7, T7 = 4000, 0.002, 10.0
kk = Kc / 2
Vc = vac.copy()
Hx = [np.array([1.0, 0, 0, 0]), np.array([0, 0, 1.0, 0])]
rbar = np.zeros((n7, 4))
rbar[:, 0] = 1.0                                # coherent state displaced to <x1> = 1
cross_max = 0.0
for _ in range(int(round(T7 / dt7))):
    dW7 = r7.normal(0, math.sqrt(dt7), size=(n7, 2))
    gain = [2 * math.sqrt(kk) * (Vc @ e) for e in Hx]                  # 2 sqrt(k) V e_x
    xhat = rbar[:, [0, 2]] * dt7 + dW7 / (2 * math.sqrt(kk))           # record estimates x_hat dt
    rnew = rbar + rbar @ A0m.T * dt7 + np.outer(dW7[:, 0], gain[0]) + np.outer(dW7[:, 1], gain[1])
    rnew[:, 1] += Kc * xhat[:, 1]                                       # feedback force on 1 from 2's record
    rnew[:, 3] += Kc * xhat[:, 0]
    rbar = rnew
    Vc = Vc + (A0m @ Vc + Vc @ A0m.T + np.diag([0, kk, 0, kk])) * dt7 - 4 * kk * sum(np.outer(Vc @ e, Vc @ e) for e in Hx) * dt7
    cross_max = max(cross_max, np.abs(Vc[:2, 2:]).max())
ts_me = np.array([0.0, T7])
sig_me = lyap_series(vac, Amat, np.diag([0, Dk(kk), 0, Dk(kk)]), np.linspace(0, T7, 2001))[-1]
mean_me = expm(Amat * T7) @ np.array([1.0, 0, 0, 0])
avg_cm = Vc + np.cov(rbar.T, bias=True)
se_cm = np.sqrt((np.outer(np.diag(sig_me), np.diag(sig_me)) + sig_me**2) / n7)
zmean = np.abs(rbar.mean(axis=0) - mean_me) / (rbar.std(axis=0) / math.sqrt(n7))
check("per trajectory the conditional covariance stays block-diagonal (product state, log-negativity 0): max |cross block|", cross_max, 0,
      atol=1e-300)
check("per trajectory the conditional state of each mass stays pure: 4 det V_1", 4 * np.linalg.det(Vc[:2, :2]), 1.0, rtol=1e-3)
check("mean dynamics match the quantum coupling: largest |z| of the 4 trajectory-averaged means at T = 10", zmean.max(), 0, atol=4.5)
check("averaged covariance = master-equation covariance (quantum coupling + diffusion D(k)): largest |z| over elements", np.max(
    np.abs(avg_cm - sig_me) / se_cm), 0, atol=5.0)
G4["trajectories"] = {"n": n7, "dt": dt7, "T": T7, "k": kk, "max_z_means": zmean.max(), "max_z_cov": np.max(np.abs(avg_cm - sig_me) / se_cm),
                      "max_cross_block": cross_max}
# physical instance and the qubit version
K_phys = 2 * G * m_b**2 / d_b**3
Gam_osc = K_phys * dx_b**2 / (2 * hbar)
G4["instance"] = {"K_N_per_m": K_phys, "D_min_hbarK": hbar * K_phys, "Gamma_min_dx250um_per_s": Gam_osc,
                  "qubit_KTM_min_omega_over_2_per_s": Mb["omega"] / 2, "Bridge_B_per_s": lam_B,
                  "ratio_bridgeB_over_KTM_qubit": lam_B / (Mb["omega"] / 2)}
check("instance: K = 2 G m^2 / d^3 (KTM Eq. 5), N/m", K_phys, 1.465e-28, rtol=2e-3)
check("linearised KTM minimum K dx^2/(2 hbar) = qubit minimum omega/2 x (d^2 - dx^2)/d^2 (same physics, exact 1/r vs linearised)",
      Gam_osc, (Mb["omega"] / 2) * (d_b**2 - dx_b**2) / d_b**2, rtol=1e-9)
print(f"     KTM minimum for the BMV qubits omega/2 = {Mb['omega'] / 2:.4f} /s; linearised oscillator {Gam_osc:.4f} /s; Bridge B {lam_B:.1f} /s "
      f"({lam_B / (Mb['omega'] / 2):.0f} times the minimum)", flush=True)

# =================================================================================================================================
RES["meta"]["runtime_seconds"] = time.perf_counter() - T_START
RES["meta"]["checks_passed"] = int(sum(results))
RES["meta"]["checks_total"] = len(results)
OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text(json.dumps(fl(RES), indent=1) + "\n")
print(f"\nwrote {OUT.relative_to(Path(__file__).resolve().parents[2])} ({RES['meta']['runtime_seconds']:.0f} s)")
print(f"\n{sum(results)} of {len(results)} checks passed")
raise SystemExit(0 if all(results) else 1)
