"""GUID v6: Our theory as simulated. Hosted benchmarks: hard quantum configurations with known answers, run as content.

Run: python3 docs/simulation/hosted_benchmarks.py          (numpy and scipy only; measured 8.2 minutes on one core of a shared 4-core machine, peak
     memory 1.9 GB). Writes docs/simulation/results/hosted_benchmarks.json with every number printed here. Each check prints OK or FAIL,
     the last line counts them, and the exit code is 0 only if all pass. Lines marked INFO are reported numbers that depend on the
     machine (wall times) and are not checks. `--only B2` runs one benchmark and writes no JSON.
     BLAS is pinned to one thread unless OPENBLAS_NUM_THREADS / OMP_NUM_THREADS are set: the machine is shared, and multi-threaded
     OpenBLAS that spin-waits on oversubscribed cores was measured 20 times slower than one thread.

Hosting, as tested here (paper, Sections 4 and 13). A configuration is asserted as existence: a Hamiltonian together with the sector
that says which states exist (a conserved charge, a gauge constraint, a register subspace). The host lets it run (Lanczos iteration,
a Bogoliubov transformation, a gate sequence). Two independent witnesses then read only the existence syndrome, built from operators that
commute with the Hamiltonian, never the content:
  witness T (trust half)        integer arithmetic on every basis configuration that carries amplitude (support membership);
  witness I (information half)  the expectation value of a positive syndrome operator, in floating point (zero exactly in the sector).
Both must pass. In every benchmark an injected fault must be refused by both, and two different contents in the same sector get the
same verdict. The known results below are reproduced: this validates the host and this code. It tests no new physics.

  [B1] Heisenberg antiferromagnetic spin-1/2 ring, H = sum S_i.S_{i+1}. Existence: S^z_total = 0. Exact diagonalisation (Lanczos) for
       N = 8 to 24, checked against the Bethe ansatz at every N; finite-size extrapolation a + b/N^2 + c/N^4 to e0 = 1/4 - ln 2
       (Hulthen 1938); the finite-size gap closes like 1/N (gapless chain).
  [B2] Transverse-field Ising ring H = -sum Z_i Z_{i+1} - g sum X_i at L = 4000 spins, solved exactly by Jordan-Wigner and a Bogoliubov
       (singular-value) transformation in the even-parity sector, where the ring's fermions are antiperiodic. Existence: fermion
       parity prod X_i = +1 and a pure Gaussian state. Ground-state energy against the finite-L closed form and the elliptic-integral
       limit (Pfeuty 1970); central charge c = 1/2 from the Casimir energy and from the Calabrese-Cardy fit of the block entropy at g = 1;
       area law at g = 0.5 and 1.5 against the corner-transfer-matrix saturation values.
  [B3] Schwinger model (QED in 1+1 dimensions), Kogut-Susskind staggered fermions, open boundaries, Gauss's law integrated out, zero
       background field (Banuls et al. 2013, Eq. 2.6). Existence: Gauss's law at every site, zero field beyond the last site, total
       charge zero. Exact diagonalisation for N = 8 to 22 at x = 1/(ag)^2 = 0.5 to 4, extrapolated N -> infinity, then x -> infinity,
       to the vector mass M/g = 1/sqrt(pi) (Schwinger 1962). Main lattice: the massless point at m_lat = -g^2 a/8 (Dempsey, Klebanov,
       Pufu, Zan 2022); the naive m_lat = 0 lattice is run too. Gauss's-law elimination checked against explicit links at N = 6; the
       finite-size form tested out of sample at N = 24.
  [B4] Shor's period finding on an exact statevector: N = 15, 21, 33, 35, 39, 51, 55, 57 with every base, and N = 143 (24 qubits).
       Existence: unit norm and the work register inside {0, ..., N-1}. Outcome distributions against Shor's analytic distribution,
       success probabilities, qubit counts. Cost map of dense statevector simulation for n = 10 to 26 qubits and its 2^n law,
       extrapolated to n = 50, 4000 and 4099 (a 2048-bit RSA modulus with Beauregard's 2n + 3 circuit).

Uncertainties. An extrapolated number carries the largest change over a family of alternative fits fixed in this code (windows and
forms), combined in quadrature with the propagated error where there is one; such a check passes when the deviation from the known value
is at most twice that uncertainty. Tolerances of exact identities are set by floating-point accuracy and are stated with each check.
"""

import os

for _v in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")

import json  # noqa: E402
import math  # noqa: E402
import platform  # noqa: E402
import resource  # noqa: E402
import sys  # noqa: E402
import time  # noqa: E402
import tracemalloc  # noqa: E402
from pathlib import Path  # noqa: E402

import numpy as np  # noqa: E402
import scipy  # noqa: E402
import scipy.sparse as sp  # noqa: E402
import scipy.sparse.linalg as sla  # noqa: E402
from scipy.special import ellipe, ellipk  # noqa: E402

OUT = Path(__file__).resolve().parent / "results" / "hosted_benchmarks.json"
results = []
CHECKS = []
R = {}


def check(label, got, want, rtol=None, atol=None):
    """OK if abs(got - want) <= tolerance; the tolerance is atol, or rtol * abs(want), or the larger if both are given."""
    got, want = float(got), float(want)
    if rtol is None and atol is None:
        rtol = 1e-6
    tol = max(atol or 0.0, (rtol or 0.0) * abs(want))
    ok = abs(got - want) <= tol
    print(f"{'OK  ' if ok else 'FAIL'} {label}: {got:.10g} (expected {want:.10g}, tolerance {tol:.2g})")
    results.append(ok)
    CHECKS.append({"label": label, "got": got, "expected": want, "tolerance": tol, "pass": ok})


def check_true(label, cond):
    print(f"{'OK  ' if cond else 'FAIL'} {label}")
    results.append(bool(cond))
    CHECKS.append({"label": label, "pass": bool(cond)})


def info(label, value):
    print(f"INFO {label}: {value}")


def peak_rss_gb():
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6   # Linux reports kB


# ---------------------------------------------------------------------------------------------------------------------------------
# Shared host machinery: computational basis states as integers (bit k = site k up / occupied), sector bases, Lanczos.
POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


def popcount_lut(a):
    """Host's popcount: byte lookup table."""
    a = np.asarray(a).astype(np.uint64)
    c = np.zeros(a.shape, dtype=np.int64)
    for s in range(0, 64, 8):
        c += POP8[((a >> np.uint64(s)) & np.uint64(0xFF)).astype(np.intp)]
    return c


def popcount_swar(a):
    """Witnesses' popcount: a different algorithm (SWAR bit arithmetic), so host and witness share no code path."""
    v = np.asarray(a).astype(np.uint64)
    m1, m2, m4, h01 = (np.uint64(x) for x in (0x5555555555555555, 0x3333333333333333, 0x0F0F0F0F0F0F0F0F, 0x0101010101010101))
    v = v - ((v >> np.uint64(1)) & m1)
    v = (v & m2) + ((v >> np.uint64(2)) & m2)
    v = (v + (v >> np.uint64(4))) & m4
    return ((v * h01) >> np.uint64(56)).astype(np.int64)


def sector_states(N, n_up):
    allst = np.arange(1 << N, dtype=np.int64)
    return allst[popcount_lut(allst) == n_up]


def hop_matrix(states, bonds):
    """Sparse matrix of sum over bonds of (s+_i s-_j + s-_i s+_j) in a fixed-magnetisation basis (all matrix elements 1)."""
    rows, cols = [], []
    for i, j in bonds:
        sel = np.nonzero(((states >> i) ^ (states >> j)) & 1)[0]
        rows.append(sel.astype(np.int32))
        cols.append(np.searchsorted(states, states[sel] ^ ((1 << i) | (1 << j))).astype(np.int32))
    r, c = np.concatenate(rows), np.concatenate(cols)
    D = len(states)
    return sp.csr_matrix((np.ones(len(r)), (r, c)), shape=(D, D))


def lowest_two(T, coef, diag, v0, ncv=40, tol=1e-10):
    """Two lowest eigenpairs of coef * T + diag(diag): dense for small dimension, implicitly restarted Lanczos (ARPACK) otherwise."""
    D = T.shape[0]
    if D <= 3000:
        w, V = np.linalg.eigh((coef * T + sp.diags(diag)).toarray())
        return w[:2], V[:, :2], 0
    count = [0]

    def mv(v):
        count[0] += 1
        return coef * (T @ v) + diag * v

    op = sla.LinearOperator((D, D), matvec=mv, dtype=np.float64)
    w, V = sla.eigsh(op, k=2, which="SA", v0=v0, ncv=ncv, tol=tol)
    o = np.argsort(w)
    return w[o], V[:, o], count[0]


def lsq(X, y, weights=None):
    w = np.ones(len(y)) if weights is None else np.asarray(weights, float)
    A, b = X * w[:, None], y * w
    coef = np.linalg.lstsq(A, b, rcond=None)[0]
    cov = np.linalg.pinv(A.T @ A)
    return coef, cov


def inv_power_fit(Ns, y, powers):
    """Fit y = a + sum_p c_p / N^p; returns all coefficients (a first)."""
    Ns = np.asarray(Ns, float)
    X = np.column_stack([np.ones(len(Ns))] + [1.0 / Ns**p for p in powers])
    return lsq(X, np.asarray(y, float))[0]


def pauli_full(N, site_ops):
    """Dense 2^N operator, product of single-site 2x2 operators {site: op}; bit k of the basis index is site k (1 = up)."""
    m = np.ones((1, 1))
    for k in reversed(range(N)):
        m = np.kron(m, site_ops.get(k, np.eye(2)))
    return m


SZ = np.diag([-0.5, 0.5])             # basis order |0> = down, |1> = up
SP = np.array([[0.0, 0.0], [1.0, 0.0]])   # S+ |down> = |up>
SM = SP.T


# ---------------------------------------------------------------------------------------------------------------------------------
def bethe_ground_energy(N, tol=1e-13):
    """Ground-state energy of the periodic Heisenberg ring from the Bethe ansatz: M = N/2 real rapidities,
    N arctan(2 l_j) = pi I_j + sum_k arctan(l_j - l_k), I_j = -(M-1)/2, ..., (M-1)/2;  E = N/4 - sum_j 2 / (1 + 4 l_j^2)."""
    M = N // 2
    I = -(M - 1) / 2 + np.arange(M)
    lam = 0.5 * np.tan(np.pi * I / N)
    for _ in range(100):
        d = lam[:, None] - lam[None, :]
        F = N * np.arctan(2 * lam) - np.arctan(d).sum(1) - np.pi * I
        J = 1.0 / (1.0 + d**2)
        np.fill_diagonal(J, 0.0)
        J[np.diag_indices(M)] = 2 * N / (1 + 4 * lam**2) - J.sum(1)
        step = np.linalg.solve(J, F)
        lam -= step
        if np.max(np.abs(step)) < tol:
            break
    d = lam[:, None] - lam[None, :]
    resid = np.max(np.abs(N * np.arctan(2 * lam) - np.arctan(d).sum(1) - np.pi * I))
    return N / 4 - np.sum(2 / (1 + 4 * lam**2)), resid


def witness_T_sz(indices, amps, n_up):
    """Trust half: every configuration carrying amplitude has exactly n_up up spins (SWAR popcount)."""
    return bool(np.all(popcount_swar(indices[np.abs(amps) > 0]) == n_up))


def witness_I_sz(indices, amps, N):
    """Information half: <S^z_tot> = 0 and <(S^z_tot)^2> = 0, S^z_tot = sum_k S^z_k applied site by site; also the norm."""
    m = np.zeros(len(indices))
    for k in range(N):
        m += ((indices >> k) & 1) - 0.5
    p = np.abs(amps) ** 2
    sz2 = float(p @ m**2)
    return bool(abs(p.sum() - 1) < 1e-10 and abs(p @ m) < 1e-10 and sz2 < 1e-10), sz2


def b1():
    print("\n[B1] Heisenberg ring: S^z_total = 0 sector, exact diagonalisation N = 8..24, extrapolation to 1/4 - ln 2")
    t_start = time.perf_counter()
    e_exact = 0.25 - math.log(2)
    out = {"hamiltonian": "H = sum_i S_i . S_{i+1}, periodic, spin 1/2", "existence": "S^z_total = 0",
           "known": {"e0_inf": e_exact, "source": "Hulthen 1938 (Bethe ansatz)"}, "per_N": {}}
    Ns = list(range(8, 25, 2))
    E0, E1 = {}, {}
    keep = None
    for N in Ns:
        t0 = time.perf_counter()
        st = sector_states(N, N // 2)
        T = hop_matrix(st, [(i, (i + 1) % N) for i in range(N)])
        anti = np.zeros(len(st))
        for i in range(N):
            anti += ((st >> i) ^ (st >> ((i + 1) % N))) & 1
        diag = 0.25 * (N - 2 * anti)
        v0 = np.random.default_rng(1000 + N).standard_normal(len(st))
        w, V, nmv = lowest_two(T, 0.5, diag, v0, tol=1e-12)
        E0[N], E1[N] = w[0], w[1]
        eb, resid = bethe_ground_energy(N)
        out["per_N"][N] = {"dim": len(st), "nnz": int(T.nnz), "E0": w[0], "E1": w[1], "E0_per_site": w[0] / N, "gap": w[1] - w[0],
                           "N_gap": N * (w[1] - w[0]), "E0_bethe": eb, "bethe_residual": resid, "matvecs": nmv,
                           "seconds": time.perf_counter() - t0}
        if N == Ns[-1]:
            keep = (st, V)
        del T
    check("Bethe ansatz = exact diagonalisation, max over N = 8..24 of abs(E0_ED - E0_BA) / N (tolerance: Lanczos tol 1e-12)",
          max(abs(E0[N] - out["per_N"][N]["E0_bethe"]) / N for N in Ns), 0.0, atol=1e-9)

    # The syndrome commutes with H, and the sector holds the ground state: full 2^10 space at N = 10.
    N = 10
    H = sum(pauli_full(N, {i: SZ, (i + 1) % N: SZ}) + 0.5 * pauli_full(N, {i: SP, (i + 1) % N: SM})
            + 0.5 * pauli_full(N, {i: SM, (i + 1) % N: SP}) for i in range(N))
    Sz = sum(pauli_full(N, {i: SZ}) for i in range(N))
    check("[H, S^z_total] = 0 on the full 2^10 space (max matrix element)", np.abs(H @ Sz - Sz @ H).max(), 0.0, atol=1e-12)
    check("full-space ground energy at N = 10 = S^z = 0 sector ground energy", np.linalg.eigvalsh(H)[0], E0[10], rtol=1e-12)

    # Finite-size extrapolation: main a + b/N^2 + c/N^4 on N >= 12; alternatives fixed here.
    e = {N: E0[N] / N for N in Ns}

    def fit(nmin, powers):
        sel = [N for N in Ns if N >= nmin]
        return inv_power_fit(sel, [e[N] for N in sel], powers)

    main = fit(12, (2, 4))
    alts = {f"Nmin={nmin}, powers={p}": fit(nmin, p)[0] for nmin in (8, 10, 14, 16) for p in [(2, 4)]}
    alts.update({f"Nmin={nmin}, powers={(2, 4, 6)}": fit(nmin, (2, 4, 6))[0] for nmin in (8, 10, 12, 14, 16)})
    sigma = max(abs(v - main[0]) for v in alts.values())
    out["extrapolation"] = {"main_form": "a + b/N^2 + c/N^4, N = 12..24", "a": main[0], "b": main[1], "c": main[2],
                            "alternatives": alts, "sigma_sys": sigma, "deviation": main[0] - e_exact,
                            "deviation_over_sigma": (main[0] - e_exact) / sigma, "relative_deviation": (main[0] - e_exact) / abs(e_exact)}
    print(f"     extrapolated e0 = {main[0]:.10f} +- {sigma:.1e} (fit-family spread), exact {e_exact:.10f}, "
          f"deviation {main[0] - e_exact:+.2e} = {(main[0] - e_exact) / sigma:+.2f} sigma")
    check("e0 = a (N -> infinity) against 1/4 - ln 2, within 2 sigma of the fit family", main[0], e_exact, atol=2 * sigma)
    c_cas = -12 * main[1] / math.pi**2   # b = -pi v c / 6 with v = pi/2
    out["extrapolation"]["c_from_b"] = c_cas
    info("CFT reading of b: c = -12 b / pi^2 (expected 1 up to logarithmic corrections)", f"{c_cas:.4f}")

    # Gap: closes like 1/N (gapless), N * gap drifts to pi^2/2 with logarithmic corrections.
    gap = np.array([E1[N] - E0[N] for N in Ns])
    Na = np.array(Ns, float)
    p_loc = -np.diff(np.log(gap)) / np.diff(np.log(Na))
    sel = Na >= 12
    gfit = inv_power_fit(Na[sel], gap[sel], (1, 2))
    out["gap"] = {"N": Ns, "gap": gap, "N_gap": Na * gap, "local_exponent": p_loc, "fit_a_b_over_N_c_over_N2": gfit,
                  "pi2_over_2": math.pi**2 / 2}
    print(f"     N * gap: {np.round(Na * gap, 4).tolist()}  (pi^2/2 = {math.pi**2 / 2:.4f} only as N -> infinity, log corrections)")
    check_true(f"gap closes like a power of N: local exponent d ln(gap)/d ln N at N = 22..24 is {p_loc[-1]:.3f} > 0.9, "
               f"and rises with N", p_loc[-1] > 0.9 and np.all(np.diff(p_loc) > 0))
    check_true(f"extrapolated gap (a + b/N + c/N^2, N >= 12) = {gfit[0]:.4f} is below 10% of the N = 24 gap {gap[-1]:.4f} "
               f"(a gapped chain would keep it)", abs(gfit[0]) < 0.1 * gap[-1])

    # Witnesses on the N = 24 states, embedded in the full 2^24 register.
    st, V = keep
    N = Ns[-1]
    verdicts = {}
    for name, amps, idx in [("ground state", V[:, 0], st), ("first excited state (triplet)", V[:, 1], st),
                            ("fault: sigma^x on site 0 applied to the ground state", V[:, 0], st ^ 1)]:
        tv = witness_T_sz(idx, amps, N // 2)
        iv, sz2 = witness_I_sz(idx, amps, N)
        verdicts[name] = {"witness_T": tv, "witness_I": iv, "<Sz_tot^2>": sz2}
    out["witnesses"] = verdicts
    check_true("both witnesses pass the hosted ground state (N = 24)", verdicts["ground state"]["witness_T"] and verdicts["ground state"]["witness_I"])
    check_true("a different content in the same sector (the triplet, orthogonal: overlap "
               f"{abs(V[:, 0] @ V[:, 1]):.1e}) gets the same verdict", verdicts["first excited state (triplet)"]["witness_T"]
               and verdicts["first excited state (triplet)"]["witness_I"] and abs(V[:, 0] @ V[:, 1]) < 1e-8)
    f = verdicts["fault: sigma^x on site 0 applied to the ground state"]
    check_true(f"both witnesses refuse a single spin flip (<Sz_tot^2> = {f['<Sz_tot^2>']:.3f})", not f["witness_T"] and not f["witness_I"])
    out["seconds"] = time.perf_counter() - t_start
    out["peak_rss_gb_so_far"] = peak_rss_gb()
    info("B1 runtime, s", f"{out['seconds']:.1f}")
    R["B1"] = out


# ---------------------------------------------------------------------------------------------------------------------------------
def tfim_K(L, g):
    """H = i sum_jk K_jk a_j b_k with Majoranas a_j = (prod_{l<j} X_l) Z_j, b_j = (prod_{l<j} X_l) Y_j:
    X_j = i a_j b_j, Z_j Z_{j+1} = i b_j a_{j+1}; in the even-parity sector the wrap bond is antiperiodic."""
    K = -g * np.eye(L)
    K[np.arange(1, L), np.arange(L - 1)] = 1.0
    K[0, L - 1] = -1.0
    return K


def tfim_ground(L, g):
    U, s, Vt = np.linalg.svd(tfim_K(L, g))
    return -s.sum(), -(U @ Vt), s          # E0, G_jk = <i a_j b_k>, single-particle energies / 2


def block_entropy(G, l):
    nu = np.clip(np.linalg.svd(G[:l, :l], compute_uv=False), 0.0, 1.0)
    p, q = (1 + nu) / 2, (1 - nu) / 2
    with np.errstate(divide="ignore", invalid="ignore"):
        h = -np.where(p > 0, p * np.log(p), 0.0) - np.where(q > 0, q * np.log(q), 0.0)
    return float(h.sum())


def parity_lu(G):
    """Witness T: parity = det G = <prod_j X_j> via pivoted LU; purity: |det G| = 1."""
    s, logabs = np.linalg.slogdet(G)
    return float(s), float(logabs)


def parity_qr(G):
    """Witness I: parity = det G via Householder QR, det Q = (-1)^(number of reflectors), det R = prod diag; purity: G G^T = 1."""
    h, tau = np.linalg.qr(G, mode="raw")
    d = np.diag(h)
    sign = (-1.0) ** int(np.count_nonzero(tau)) * float(np.prod(np.sign(d)))
    return sign, float(np.sum(np.log(np.abs(d))))


def ctm_saturation(g):
    """Block entropy of a long block in an infinite chain, from the corner transfer matrix (Calabrese and Cardy 2004, Eqs. 4.30-4.34,
    their lambda = 1/g): eps = pi K(k') / K(k), k = min(g, 1/g); half-chain levels (2j+1) eps for g > 1, 2j eps for g < 1.
    A block has two cuts: g > 1 gives 2 S_half; for g < 1 the even-parity ground state is the cat state, whose ln 2 is shared by the
    two cuts, so the block has 2 S_half - ln 2."""
    k = min(g, 1 / g)
    eps = math.pi * ellipk(1 - k**2) / ellipk(k**2)
    j = np.arange(0, 400)
    lev = (2 * j + 1) * eps if g > 1 else 2 * j * eps
    with np.errstate(over="ignore"):
        s_half = float(np.sum(np.log1p(np.exp(-lev)) + lev / (np.exp(lev) + 1)))
    return (2 * s_half if g > 1 else 2 * s_half - math.log(2)), eps, s_half


def b2():
    print("\n[B2] Transverse-field Ising ring at L = 4000: Jordan-Wigner + Bogoliubov, even-parity (antiperiodic-fermion) sector")
    t_start = time.perf_counter()
    L = 4000
    out = {"hamiltonian": "H = -sum Z_i Z_{i+1} - g sum X_i, periodic ring", "L": L,
           "existence": "fermion parity prod X_i = +1 (the Jordan-Wigner map with antiperiodic fermions is exact there) and a pure Gaussian state",
           "boundary_conditions": "periodic spins = antiperiodic fermions in the even sector",
           "cc_formula": "S(l) = (c/3) ln[(L/pi) sin(pi l / L)] + c1'  (Calabrese-Cardy 2004, Eq. 1.1, periodic)"}

    # Jordan-Wigner signs and the sector: brute force at L = 10.
    Lc = 10
    X, Z = np.array([[0.0, 1.0], [1.0, 0.0]]), np.diag([1.0, -1.0])
    P = pauli_full(Lc, {k: X for k in range(Lc)})
    dev, comm = 0.0, 0.0
    for g in (0.5, 1.0, 1.5):
        H = -sum(pauli_full(Lc, {i: Z, (i + 1) % Lc: Z}) for i in range(Lc)) - g * sum(pauli_full(Lc, {i: X}) for i in range(Lc))
        comm = max(comm, np.abs(H @ P - P @ H).max())
        w, Vv = np.linalg.eigh(H)
        par = np.einsum("ij,ij->j", Vv, P @ Vv)               # <prod X> of each eigenvector (levels are non-degenerate here)
        e_even = w[np.argmax(par > 0.5)]
        dev = max(dev, abs(e_even - tfim_ground(Lc, g)[0]))
    check("[H, prod X_i] = 0 at L = 10 (max matrix element)", comm, 0.0, atol=1e-12)
    check("Bogoliubov energy (antiperiodic) = lowest even-parity spin energy at L = 10, g = 0.5, 1, 1.5 (max abs diff)", dev, 0.0, atol=1e-11)

    out["per_g"] = {}
    for g in (1.0, 0.5, 1.5):
        t0 = time.perf_counter()
        E0, G, s = tfim_ground(L, g)
        t_svd = time.perf_counter() - t0
        k = 2 * np.pi * (np.arange(L) + 0.5) / L
        E_closed = -float(np.sum(np.sqrt(1 + g * g - 2 * g * np.cos(k))))
        e_inf = -(2 / math.pi) * (1 + g) * float(ellipe(4 * g / (1 + g) ** 2))
        rec = {"E0": E0, "E0_closed_form_finite_L": E_closed, "e_inf": e_inf, "E0_per_site": E0 / L, "E0_per_site_minus_e_inf": E0 / L - e_inf,
               "gap_single_particle_min": 2 * float(s.min()), "svd_seconds": t_svd}
        print(f"  g = {g}: E0 = {E0:.10f}, closed form {E_closed:.10f}, E0/L - e_inf = {E0 / L - e_inf:.3e}")
        check(f"g = {g}: E0 against the finite-L closed form -sum_k sqrt(1 + g^2 - 2g cos k), k = 2pi(n + 1/2)/L "
              f"(relative, float accuracy)", E0, E_closed, rtol=1e-12)
        if g == 1.0:
            c_cas = -(E0 - L * e_inf) * 6 * L / (math.pi * 2.0)        # E0 = L e_inf - pi v c / (6 L), v = 2
            rec["c_casimir"] = c_cas
            check("g = 1: c from the Casimir energy, -(E0 - L e_inf) 6L / (pi v), v = 2 (tolerance 1e-7: next term 7pi^2/(480 L^2) = 9e-9)",
                  c_cas, 0.5, atol=1e-7)
            ls = np.unique(np.round(np.geomspace(1, L // 2, 60)).astype(int))
        else:
            check(f"g = {g}: E0/L = e_inf = -(2/pi)(1+g) E(4g/(1+g)^2) (gapped: finite-size terms ~ exp(-L/xi))", E0 / L, e_inf, rtol=1e-13)
            ls = np.array([1, 2, 4, 8, 16, 32, 64, 125, 250, 500, 1000, 2000])
        t0 = time.perf_counter()
        S = np.array([block_entropy(G, int(l)) for l in ls])
        rec["entropy"] = {"l": ls, "S": S, "seconds": time.perf_counter() - t0}
        if g == 1.0:
            chord = np.log(L / math.pi * np.sin(math.pi * ls / L))

            def ccfit(lmin, lmax):
                m = (ls >= lmin) & (ls <= lmax)
                (cc, c1), _ = lsq(np.column_stack([chord[m] / 3, np.ones(m.sum())]), S[m])
                return cc, c1, float(np.max(np.abs(chord[m] / 3 * cc + c1 - S[m])))

            c_main, c1_main, res_main = ccfit(100, L // 2)
            alts = {f"l in [{a}, {b}]": ccfit(a, b)[0] for a, b in [(50, L // 2), (200, L // 2), (400, L // 2), (100, L // 4)]}
            sig = max(abs(v - c_main) for v in alts.values())
            rec["cc_fit"] = {"window": [100, L // 2], "c": c_main, "c1_prime": c1_main, "max_residual": res_main, "alternatives": alts,
                             "sigma_sys": sig, "deviation": c_main - 0.5}
            print(f"     Calabrese-Cardy: c = {c_main:.9f} +- {sig:.1e}, c1' = {c1_main:.6f}, max residual {res_main:.1e}")
            check("g = 1: central charge from the Calabrese-Cardy fit, l in [100, L/2], within 2 sigma of the window family (+1e-9 float)",
                  c_main, 0.5, atol=2 * sig + 1e-9)
        else:
            s_ctm, eps, s_half = ctm_saturation(g)
            rec["area_law"] = {"S_L_over_2": S[-1], "S_L_over_8": S[ls == 500][0], "ctm_prediction": s_ctm, "ctm_eps": eps, "ctm_S_half": s_half,
                               "xi_lattice": 1 / abs(math.log(g))}
            print(f"     S(l) for l = 1..2000: {np.round(S, 6).tolist()}")
            check_true(f"g = {g}: area law, S(L/2) - S(L/8) = {S[-1] - S[ls == 500][0]:.1e} (saturated to 1e-10)",
                       abs(S[-1] - S[ls == 500][0]) < 1e-10)
            check(f"g = {g}: saturated block entropy S(L/2) against the corner-transfer-matrix value (tolerance 1e-9: float error of the "
                  f"entropy sum ~1e-11, finite-size terms exp(-2000/xi) negligible)", S[-1], s_ctm, atol=1e-9)

        # Witnesses read the existence syndrome of the hosted Gaussian state, and refuse a single spin flip Z_1 (one Majorana).
        sT, laT = parity_lu(G)
        sI, laI = parity_qr(G)
        orth = float(np.abs(G @ G.T - np.eye(L)).max())
        Gf = G.copy()
        Gf[0, :] *= -1.0            # Z_1 rho Z_1 maps <i a_1 b_k> -> -<i a_1 b_k>
        fT, fI = parity_lu(Gf)[0], parity_qr(Gf)[0]
        rec["witnesses"] = {"T_parity_lu": sT, "T_log_abs_det": laT, "I_parity_qr": sI, "I_log_abs_det": laI, "I_max_abs_GGt_minus_1": orth,
                            "fault_Z1_T_parity": fT, "fault_Z1_I_parity": fI}
        check_true(f"g = {g}: witness T (LU) reads parity {sT:+.0f}, |det| = 1 to {abs(laT):.0e}; witness I (QR) reads {sI:+.0f}, "
                   f"max|G G^T - 1| = {orth:.0e}: both pass", sT == 1.0 and sI == 1.0 and abs(laT) < 1e-10 and orth < 1e-10)
        check_true(f"g = {g}: both witnesses refuse a single spin flip Z_1 (parity {fT:+.0f}, {fI:+.0f})", fT == -1.0 and fI == -1.0)
        rec["seconds"] = time.perf_counter() - t0 + t_svd
        out["per_g"][g] = rec
        del G
    out["seconds"] = time.perf_counter() - t_start
    out["peak_rss_gb_so_far"] = peak_rss_gb()
    out["memory_note"] = "dense 4000 x 4000 float64 matrices (128 MB each): K, U, V^T, G"
    info("B2 runtime, s", f"{out['seconds']:.1f}")
    R["B2"] = out


# ---------------------------------------------------------------------------------------------------------------------------------
def schwinger_parts(N):
    """Banuls et al. 2013, Eq. 2.6 with l = 0: W = x sum_{n<N-1} (s+_n s-_{n+1} + h.c.) + (mu/2) sum_n (1 + (-1)^n s^z_n)
    + sum_{n<N-1} L_n^2, L_n = sum_{k<=n} Q_k, Q_k = (s^z_k + (-1)^k)/2; total charge zero = S^z_total = 0 sector.
    Returns the sector basis, the hopping matrix, the electric and mass diagonals and the host's link register E_0..E_{N-2}."""
    st = sector_states(N, N // 2)
    T = hop_matrix(st, [(n, n + 1) for n in range(N - 1)])
    D = len(st)
    elec, mass = np.zeros(D), np.zeros(D)
    Lcur = np.zeros(D, dtype=np.int64)
    links = np.empty((D, N - 1), dtype=np.int8)
    for k in range(N):
        s = 2 * ((st >> k) & 1) - 1
        stag = 1 if k % 2 == 0 else -1
        Lcur += (s + stag) // 2
        mass += 0.5 * (1 + stag * s)
        if k < N - 1:
            elec += Lcur.astype(np.float64) ** 2
            links[:, k] = Lcur
    return st, T, elec, mass, links


def schwinger_unintegrated(N, x, mu, Emax):
    """The same model with explicit integer link fields E_0..E_{N-2} (|E| <= Emax): hopping s+_n R_n s-_{n+1} + h.c. with R_n raising
    E_n by one, electric energy sum E_n^2. Gauss generators G_n = E_n - E_{n-1} - Q_n with E_{-1} = 0 and E_{N-1} = 0."""
    nl, base = N - 1, 2 * Emax + 1
    D = (1 << N) * base**nl
    idx = np.arange(D, dtype=np.int64)
    spins, rest = idx & ((1 << N) - 1), idx >> N
    E = np.empty((D, nl), dtype=np.int64)
    for n in range(nl):
        E[:, n] = rest % base - Emax
        rest //= base
    s = np.stack([2 * ((spins >> k) & 1) - 1 for k in range(N)], axis=1)
    stag = (-1) ** np.arange(N)
    Q = (s + stag) // 2
    Eext = np.concatenate([np.zeros((D, 1), np.int64), E, np.zeros((D, 1), np.int64)], axis=1)
    G = Eext[:, 1:] - Eext[:, :-1] - Q
    diag = (E**2).sum(1) + 0.5 * mu * (1 + s * stag).sum(1)
    rows, cols = [], []
    for n in range(nl):
        m = (((spins >> n) & 1) == 0) & (((spins >> (n + 1)) & 1) == 1) & (E[:, n] < Emax)
        src = idx[m]
        tgt = (src ^ (1 << n) ^ (1 << (n + 1))) + (base**n << N)
        rows += [tgt, src]
        cols += [src, tgt]
    r, c = np.concatenate(rows), np.concatenate(cols)
    H = sp.csr_matrix((np.full(len(r), float(x)), (r, c)), shape=(D, D)) + sp.diags(diag.astype(float))
    return H, G


def gauss_witness_T(bits, links, amps, N):
    """Trust half: integer check of Gauss's law at every site of every configuration carrying amplitude, from the stored links."""
    sel = np.abs(amps) > 0
    b, E = bits[sel], links[sel].astype(np.int64)
    ok = True
    prev = np.zeros(len(b), dtype=np.int64)                    # E_{-1} = 0: zero background field
    qtot = np.zeros(len(b), dtype=np.int64)
    for n in range(N):
        q = ((b >> n) & 1) - (n % 2)                          # Q_n: 1 for an occupied even site, -1 for an empty odd site
        qtot += q
        cur = E[:, n] if n < N - 1 else np.zeros(len(b), dtype=np.int64)   # E_{N-1} = 0: no field beyond the last site
        ok &= bool(np.all(cur - prev == q))
        prev = cur
    return ok and bool(np.all(qtot == 0))


def gauss_witness_I(bits, links, amps, N):
    """Information half: <sum_n G_n^2> + <Q_tot^2> = 0 as a weighted expectation in floating point (Q_tot from the SWAR popcount)."""
    p = np.abs(amps) ** 2
    Eext = np.concatenate([np.zeros((len(bits), 1)), links.astype(np.float64), np.zeros((len(bits), 1))], axis=1)
    g2 = np.zeros(len(bits))
    for n in range(N):
        sz = 2.0 * ((bits >> n) & 1) - 1.0
        q = 0.5 * (sz + (1.0 if n % 2 == 0 else -1.0))
        g2 += (Eext[:, n + 1] - Eext[:, n] - q) ** 2
    qtot = popcount_swar(bits) - N / 2
    val = float(p @ g2 + p @ qtot**2)
    return bool(val < 1e-10 and abs(p.sum() - 1) < 1e-10), val


def n_extrapolate(gaps):
    """gaps: {N: gap}. Main: w + a/N^2 + b/N^3 on N >= 12; alternatives fixed here. Returns main, sigma, alternatives, coefficients."""
    Ns = np.array(sorted(gaps), float)
    g = np.array([gaps[int(N)] for N in Ns])

    def fit(m, powers):
        return inv_power_fit(Ns[m], g[m], powers)

    cmain = fit(Ns >= 12, (2, 3))
    alts = {"Nmin=14": fit(Ns >= 14, (2, 3))[0], "Nmin=16": fit(Ns >= 16, (2, 3))[0], "1/N^2+1/N^4": fit(Ns >= 12, (2, 4))[0],
            "1/N^2 on last 4": fit(Ns >= Ns[-4], (2,))[0]}
    return cmain[0], max(abs(v - cmain[0]) for v in alts.values()), alts, cmain


def continuum(xs, w, s, allow_no_linear):
    """M/g(x) = M + c1 y + c2 y^2, y = 1/sqrt(x), weighted by the N-extrapolation errors; alternatives fixed here."""
    xs, w, s = np.asarray(xs, float), np.asarray(w, float), np.maximum(np.asarray(s, float), 1e-6)
    y = 1 / np.sqrt(xs)

    def fit(m, powers):
        coef, cov = lsq(np.column_stack([np.ones(m.sum())] + [y[m] ** p for p in powers]), w[m], 1 / s[m])
        return coef, math.sqrt(cov[0, 0])

    allm = np.ones(len(xs), bool)
    (cm, sm) = fit(allm, (1, 2))
    alts = {"linear, x >= 1.5": fit(xs >= 1.5, (1,))[0][0], "quadratic, x >= 1": fit(xs >= 1, (1, 2))[0][0],
            "cubic": fit(allm, (1, 2, 3))[0][0]}
    if allow_no_linear:
        alts["no linear term"] = fit(allm, (2,))[0][0]
    ssys = max(abs(v - cm[0]) for v in alts.values())
    return {"M": cm[0], "coefficients": cm, "sigma_stat": sm, "sigma_sys": ssys, "sigma": math.hypot(sm, ssys), "alternatives": alts}


def b3():
    print("\n[B3] Schwinger model: Kogut-Susskind lattice, Gauss's law integrated out, open boundaries, zero background, zero charge")
    t_start = time.perf_counter()
    M_exact = 1 / math.sqrt(math.pi)
    out = {"hamiltonian": "W = 2H/(a g^2) = x sum (s+_n s-_{n+1} + h.c.) + (mu/2) sum (1 + (-1)^n s^z_n) + sum_{n<N-1} L_n^2 (Banuls et al. 2013, Eq. 2.6, l = 0)",
           "parameters": "x = 1/(ag)^2, mu = 2 m_lat / (a g^2); M/g = (E1 - E0) / (2 sqrt x)",
           "existence": "Gauss's law L_n - L_{n-1} = Q_n at every site with L_{-1} = 0 (zero background) and L_{N-1} = 0 (zero field beyond the last site); total charge 0",
           "lattices": {"shifted (main)": "mu = -1/4, i.e. m_lat = -g^2 a / 8 (Dempsey et al. 2022): continuum m = 0",
                        "naive": "mu = 0, m_lat = 0"},
           "known": {"M_over_g": M_exact, "source": "Schwinger 1962", "MPS_reference": "0.56421(9), Banuls et al. 2013"}}

    # Code check: the Gauss-law elimination against explicit links (N = 6, |E| <= 3 is exact there), generic x and mu.
    H, G = schwinger_unintegrated(6, 1.3, 0.37, 3)
    comm = max(abs(H @ sp.diags(G[:, n].astype(float)) - sp.diags(G[:, n].astype(float)) @ H).max() for n in range(6))
    phys = np.nonzero((G == 0).all(1))[0]
    st6, T6, el6, ma6, _ = schwinger_parts(6)
    spec_dev = np.abs(np.linalg.eigvalsh(H[phys][:, phys].toarray()) - np.linalg.eigvalsh((1.3 * T6 + sp.diags(el6 + 0.37 * ma6)).toarray())).max()
    out["gauss_code_check"] = {"N": 6, "Emax": 3, "dim_explicit": H.shape[0], "physical_states": len(phys), "max_commutator": comm, "max_spectrum_diff": spec_dev}
    check("explicit links, N = 6: max over n of |[H, G_n]| (Gauss generators commute with H)", comm, 0.0, atol=1e-12)
    check(f"explicit links, N = 6: the {len(phys)} states with G_n = 0 have the spectrum of the integrated Hamiltonian (max abs diff)",
          spec_dev, 0.0, atol=1e-10)
    del H, G

    XS = [4, 3, 2, 1.5, 1, 0.5]
    MUS = {"shifted": -0.25, "naive": 0.0}
    Ns = list(range(8, 23, 2))
    data = {name: {x: {} for x in XS} for name in MUS}
    e0s = {name: {x: {} for x in XS} for name in MUS}
    meta = {}
    keep = None
    for N in Ns:
        t0 = time.perf_counter()
        st, T, elec, mass, links = schwinger_parts(N)
        nmv = 0
        for name, mu in MUS.items():
            v0 = np.random.default_rng(2000 + N).standard_normal(len(st))
            for x in XS:                                    # warm start: each x starts from the previous x's two states
                w, V, c = lowest_two(T, x, elec + mu * mass, v0)
                nmv += c
                v0 = V[:, 0] + V[:, 1]
                data[name][x][N] = (w[1] - w[0]) / (2 * math.sqrt(x))
                e0s[name][x][N] = w[0]
                if N == Ns[-1] and name == "shifted" and x == 1:
                    keep = (st.copy(), links.copy(), V.copy())
        meta[N] = {"dim": len(st), "nnz": int(T.nnz), "matvecs": nmv, "seconds": time.perf_counter() - t0}
        del T
    out["per_N"] = meta
    out["gaps_M_over_g"] = {name: {x: dict(data[name][x]) for x in XS} for name in MUS}
    out["E0"] = {name: {x: dict(e0s[name][x]) for x in XS} for name in MUS}

    out["thermodynamic_limit"], out["continuum"] = {}, {}
    for name in MUS:
        rows = {}
        for x in XS:
            wv, sv, alts, coef = n_extrapolate(data[name][x])
            rows[x] = {"M_over_g": wv, "sigma_N": sv, "alternatives": alts, "coefficients": coef, "N_max_over_sqrt_x": Ns[-1] / math.sqrt(x)}
        out["thermodynamic_limit"][name] = rows
        used = [x for x in XS if Ns[-1] / math.sqrt(x) >= 10]       # physical volume N a g >= 10 (about 5.6 vector Compton lengths)
        cont = continuum(used, [rows[x]["M_over_g"] for x in used], [rows[x]["sigma_N"] for x in used], allow_no_linear=(name == "shifted"))
        cont["x_used"] = used
        cont["deviation"] = cont["M"] - M_exact
        cont["deviation_over_sigma"] = cont["deviation"] / cont["sigma"]
        out["continuum"][name] = cont
        print(f"  {name} lattice (mu = {MUS[name]}): N -> infinity at each x (N = 12..22):")
        for x in XS:
            print(f"     x = {x:>3}: M/g = {rows[x]['M_over_g']:.5f} +- {rows[x]['sigma_N']:.5f}   (N = 22: {data[name][x][22]:.5f})")
        print(f"     continuum x -> infinity: M/g = {cont['M']:.4f} +- {cont['sigma']:.4f} (stat {cont['sigma_stat']:.4f}, fit family "
              f"{cont['sigma_sys']:.4f}); 1/sqrt(pi) = {M_exact:.5f}; deviation {cont['deviation']:+.4f} = {cont['deviation_over_sigma']:+.2f} sigma")
        check(f"{name} lattice: vector mass M/g in the continuum against 1/sqrt(pi), within 2 sigma", cont["M"], M_exact, atol=2 * cont["sigma"])

    # Out-of-sample test of the finite-size form: predict N = 24 at the hardest x from the N <= 22 fit, then compute it.
    t0 = time.perf_counter()
    x, mu, N = 4, -0.25, 24
    st, T, elec, mass, _ = schwinger_parts(N)
    w, _, c = lowest_two(T, x, elec + mu * mass, np.random.default_rng(2024).standard_normal(len(st)))
    actual = (w[1] - w[0]) / (2 * math.sqrt(x))
    coef = out["thermodynamic_limit"]["shifted"][x]["coefficients"]
    pred = coef[0] + coef[1] / N**2 + coef[2] / N**3
    sN = out["thermodynamic_limit"]["shifted"][x]["sigma_N"]
    out["out_of_sample_N24"] = {"x": x, "mu": mu, "dim": len(st), "nnz": int(T.nnz), "matvecs": c, "predicted": pred, "computed": actual,
                                "difference": pred - actual, "sigma_N": sN, "seconds": time.perf_counter() - t0}
    del T, st, elec, mass
    check(f"out of sample: the N = 12..22 fit predicts the N = 24 gap at x = 4 (shifted), within sigma_N(x = 4) = {sN:.4f}", pred, actual, atol=sN)

    # Witnesses on the N = 22 ground state and vector state (x = 1, shifted), with the host's explicit link register.
    st, links, V = keep
    N = Ns[-1]
    ver = {}
    linkfault = links.copy()
    linkfault[:, N // 2] += 1
    for name, amps, bits, lk in [("ground state", V[:, 0], st, links), ("vector state", V[:, 1], st, links),
                                 ("fault: spin flip at site 0 (a charge without its field)", V[:, 0], st ^ 1, links),
                                 (f"fault: flux +1 on link {N // 2} without charges", V[:, 0], st, linkfault)]:
        tv = gauss_witness_T(bits, lk, amps, N)
        iv, val = gauss_witness_I(bits, lk, amps, N)
        ver[name] = {"witness_T": tv, "witness_I": iv, "<sum G_n^2 + Q_tot^2>": val}
    out["witnesses"] = ver
    check_true("both witnesses pass the hosted ground state (N = 22, x = 1)", ver["ground state"]["witness_T"] and ver["ground state"]["witness_I"])
    check_true(f"the vector state (orthogonal content, overlap {abs(V[:, 0] @ V[:, 1]):.1e}) gets the same verdict",
               ver["vector state"]["witness_T"] and ver["vector state"]["witness_I"])
    for name in list(ver)[2:]:
        check_true(f"both witnesses refuse the {name} (<sum G^2 + Q^2> = {ver[name]['<sum G_n^2 + Q_tot^2>']:.2f})",
                   not ver[name]["witness_T"] and not ver[name]["witness_I"])
    out["not_done"] = {"massive_case": "not run: the ED continuum error (several per cent) cannot test the MPS values (5e-5) meaningfully",
                       "chiral_condensate": "not run: needs the free-theory subtraction and a continuum control that N <= 22 does not give"}
    out["seconds"] = time.perf_counter() - t_start
    out["peak_rss_gb_so_far"] = peak_rss_gb()
    info("B3 runtime, s", f"{out['seconds']:.1f}")
    R["B3"] = out


# ---------------------------------------------------------------------------------------------------------------------------------
def mult_order(a, N):
    r, y = 1, a % N
    while y != 1:
        y, r = y * a % N, r + 1
    return r


def shor_state(N, a, gate_level_qft=False):
    """Counting register of t = 2n qubits in uniform superposition, work register of n qubits in |1>; controlled U^(2^j) with
    U|y> = |a y mod N> for y < N and |y> otherwise (a permutation, so the register subspace y < N is invariant); inverse QFT."""
    n = math.ceil(math.log2(N))
    t = 2 * n
    Q, W = 1 << t, 1 << n
    psi = np.zeros((Q, W), dtype=np.complex128)
    psi[:, 1] = 1 / math.sqrt(Q)
    xs = np.arange(Q)
    for j in range(t):
        m = pow(a, 1 << j, N)
        perm = np.arange(W)
        perm[:N] = (m * np.arange(N)) % N
        inv = np.empty(W, dtype=np.int64)
        inv[perm] = np.arange(W)
        rows = ((xs >> j) & 1) == 1
        psi[rows] = psi[rows][:, inv]
    psi = iqft_gates(psi, t) if gate_level_qft else np.fft.fft(psi, axis=0, norm="ortho")
    return psi, n, t


def iqft_gates(psi, t):
    """Inverse QFT as a circuit: the textbook QFT (H, controlled R_k, final swaps) with every phase conjugated, QFT^dagger = QFT^*."""
    W = psi.shape[1]
    s = psi.reshape((2,) * t + (W,)).copy()          # axis 0 = most significant counting bit
    Hm = np.array([[1, 1], [1, -1]]) / math.sqrt(2)
    for j in range(t):
        s = np.moveaxis(np.tensordot(Hm, s, axes=([1], [j])), 0, j)
        for k in range(2, t - j + 1):
            idx = [slice(None)] * (t + 1)
            idx[j], idx[j + k - 1] = 1, 1
            s[tuple(idx)] *= np.exp(-2j * math.pi / 2**k)
    return np.transpose(s, list(range(t))[::-1] + [t]).reshape(1 << t, W)


def shor_analytic(Q, r):
    """Shor (1997): P(k) = Q^-2 sum_{x0 < r} |sum_{j < m(x0)} exp(-2 pi i j r k / Q)|^2, m(x0) = floor((Q - 1 - x0)/r) + 1."""
    th = 2 * np.pi * r * np.arange(Q) / Q
    sn = np.sin(th / 2)
    P = np.zeros(Q)
    for x0 in range(r):
        m = (Q - 1 - x0) // r + 1
        with np.errstate(divide="ignore", invalid="ignore"):
            P += np.where(np.abs(sn) < 1e-12, float(m * m), np.sin(m * th / 2) ** 2 / sn**2)
    return P / Q**2


def period_from_outcome(k, Q, N, a):
    """Continued-fraction convergents of k/Q; the first denominator q < N with a^q = 1 mod N, else None (one run, textbook)."""
    if k == 0:
        return None
    num, den, h0, h1, k0, k1 = k, Q, 0, 1, 1, 0
    while den:
        q = num // den
        num, den = den, num - q * den
        h0, h1, k0, k1 = h1, q * h1 + h0, k1, q * k1 + k0
        if k1 >= N:
            return None
        if pow(a, k1, N) == 1:
            return k1
    return None


def factor_from_period(r, a, N):
    if r is None or r % 2 or pow(a, r // 2, N) == N - 1:
        return None
    f = math.gcd(pow(a, r // 2, N) - 1, N)
    return f if 1 < f < N else None


def register_witness_T(psi, N):
    """Trust half: every (counting, work) configuration carrying amplitude has work value < N, and the norm is 1."""
    xs, ys = np.nonzero(psi)
    return bool(np.all(ys < N) and abs(np.sum(np.abs(psi[xs, ys]) ** 2) - 1) < 1e-12)


def register_witness_I(psi, N):
    """Information half: <psi| Pi_{y >= N} |psi> = 0 and <psi|psi> = 1, with the projector applied as an operator."""
    proj = (np.arange(psi.shape[1]) >= N).astype(float)
    leak = float(np.vdot(psi, psi * proj[None, :]).real)
    return bool(leak < 1e-12 and abs(np.vdot(psi, psi).real - 1) < 1e-12), leak


CH = 1 << 18


def haar_1q(rng):
    z = (rng.standard_normal((2, 2)) + 1j * rng.standard_normal((2, 2))) / math.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))


def apply_1q(psi, q, u):
    """Single-qubit gate on qubit q of a dense statevector, in place, in chunks of at most 2^18 amplitudes."""
    v = psi.reshape(-1, 2, 1 << q)
    A, B = v.shape[0], v.shape[2]
    if B >= A:
        step = max(1, CH // A)
        sls = [(slice(None), slice(s, s + step)) for s in range(0, B, step)]
    else:
        step = max(1, CH // B)
        sls = [(slice(s, s + step), slice(None)) for s in range(0, A, step)]
    for sa, sb in sls:
        a0, a1 = v[sa, 0, sb], v[sa, 1, sb]
        t0 = u[0, 0] * a0 + u[0, 1] * a1
        a1 *= u[1, 1]
        a1 += u[1, 0] * a0
        a0[...] = t0


def random_layer(psi, n, rng):
    for q in range(n):
        apply_1q(psi, q, haar_1q(rng))
    for q in range(n - 1):                           # CZ on (q, q+1): a sign on the |11> block, in place
        psi.reshape(-1, 2, 2, 1 << q)[:, 1, 1, :] *= -1


def b4():
    print("\n[B4] Shor's period finding on an exact statevector; the cost of dense statevector simulation")
    t_start = time.perf_counter()
    out = {"existence": "unit norm and work register value y < N (the computational subspace the modular multiplication permutes)",
           "registers": "counting t = 2n qubits, work n = ceil(log2 N) qubits, total 3n; Beauregard (2003) circuit: 2n + 3",
           "postprocessing": "one run: continued fractions of k / 2^t, first convergent denominator q < N with a^q = 1 mod N; "
                             "factor gcd(a^(r/2) - 1, N) if r is even and a^(r/2) != -1 mod N",
           "per_N": {}}

    # The inverse QFT as an explicit gate circuit equals the exact DFT used below.
    dq = max(np.abs(shor_state(15, 7, True)[0] - shor_state(15, 7)[0]).max(), np.abs(shor_state(21, 2, True)[0] - shor_state(21, 2)[0]).max())
    out["iqft_gate_vs_fft_max_abs_diff"] = dq
    check("inverse QFT as a gate circuit (H, controlled phases, swaps) = exact DFT, N = 15 and 21 (max abs amplitude diff)", dq, 0.0, atol=1e-12)

    rng = np.random.default_rng(15)
    cases = {N: None for N in (15, 21, 33, 35, 39, 51, 55, 57)}
    cases[143] = (2, 3, 5, 7)
    all_tv, all_wit, fault_ok, zfault_ok = 0.0, True, True, True
    for N, bases in cases.items():
        t0 = time.perf_counter()
        p_true = sorted(f for f in range(2, N) if N % f == 0 and all(f % d for d in range(2, f)))
        if bases is None:
            bases = tuple(a for a in range(2, N) if math.gcd(a, N) == 1)
        rec = {"known_factors": p_true, "bases": {}, "qubits_simulated": None}
        found = set()
        for a in bases:
            psi, n, t = shor_state(N, a)
            Q = 1 << t
            P = (np.abs(psi) ** 2).sum(1)
            r = mult_order(a, N)
            Pa = shor_analytic(Q, r)
            tv = 0.5 * float(np.abs(P - Pa).sum())
            all_tv = max(all_tv, tv)
            per_k = [period_from_outcome(k, Q, N, a) for k in range(Q)]
            p_per = float(sum(P[k] for k in range(Q) if per_k[k] == r))
            fac = [factor_from_period(per_k[k], a, N) for k in range(Q)]
            p_fac = float(sum(P[k] for k in range(Q) if fac[k] is not None))
            found |= {f for f in fac if f is not None} | {N // f for f in fac if f is not None}
            wt, wi = register_witness_T(psi, N), register_witness_I(psi, N)[0]
            all_wit &= wt and wi
            # Faults: a faulty multiplier that exchanges work values |1> and |2^n - 1> (2^n - 1 >= N, and |1> = a^0 always carries
            # amplitude) moves amplitude out of y < N: both must refuse. Z on work qubit 0 changes the content (a relative phase)
            # but not existence: both pass, because the syndrome never reads content.
            swap = np.arange(psi.shape[1])
            swap[[1, psi.shape[1] - 1]] = swap[[psi.shape[1] - 1, 1]]
            psi_x = psi[:, swap]
            psi_z = psi * np.where(np.arange(psi.shape[1]) & 1, -1.0, 1.0)[None, :]
            fault_ok &= (not register_witness_T(psi_x, N)) and (not register_witness_I(psi_x, N)[0])
            zfault_ok &= register_witness_T(psi_z, N) and register_witness_I(psi_z, N)[0]
            brec = {"r": r, "TV_simulated_vs_analytic": tv, "P_period_found": p_per, "P_factor_found": p_fac,
                    "P_factor_found_analytic": float(sum(Pa[k] for k in range(Q) if fac[k] is not None))}
            if a == bases[0]:
                shots = rng.choice(Q, size=1000, p=P / P.sum())
                hist = {}
                for k in shots:
                    key = str(per_k[k]) if per_k[k] is not None else "no period recovered"
                    hist[key] = hist.get(key, 0) + 1
                brec["shots_1000_recovered_period_counts"] = dict(sorted(hist.items()))
                brec["top_outcomes"] = [[int(k), float(P[k])] for k in np.argsort(P)[::-1][:8]]
            rec["bases"][a] = brec
            rec["qubits_simulated"], rec["n"], rec["t"] = t + n, n, t
            del psi, psi_x, psi_z
        rec["beauregard_qubits"] = 2 * rec["n"] + 3
        rec["factors_found"] = sorted(found)
        rec["mean_P_factor_over_bases"] = float(np.mean([b["P_factor_found"] for b in rec["bases"].values()]))
        rec["mean_P_period_over_bases"] = float(np.mean([b["P_period_found"] for b in rec["bases"].values()]))
        rec["seconds"] = time.perf_counter() - t0
        out["per_N"][N] = rec
        b0 = rec["bases"][bases[0]]
        print(f"  N = {N:>3} = {' x '.join(map(str, p_true))}: {rec['qubits_simulated']} qubits, {len(bases)} bases, a = {bases[0]}: r = {b0['r']}, "
              f"P(period) = {b0['P_period_found']:.4f}, P(factor) = {b0['P_factor_found']:.4f}; mean P(factor) over bases "
              f"{rec['mean_P_factor_over_bases']:.4f}; factors found {rec['factors_found']}")
        check_true(f"N = {N}: the factors recovered from the measured periods are the known factors {p_true}", rec["factors_found"] == p_true)
    check("all N and bases: total-variation distance between the simulated outcome distribution and Shor's analytic distribution (max)",
          all_tv, 0.0, atol=1e-10)
    check_true("all N and bases: both witnesses pass every hosted register state (norm, work register < N)", all_wit)
    check_true("all N and bases: both witnesses refuse a faulty multiplier that writes the out-of-range value 2^n - 1", fault_ok)
    check_true("all N and bases: both witnesses pass a Z fault on work qubit 0 (content changed, existence intact: the syndrome never reads content)",
               zfault_ok)

    # Cost map: dense statevector, one random layer (n Haar single-qubit gates, n - 1 CZ) per qubit count; tracemalloc counts numpy buffers.
    rng = np.random.default_rng(26)
    cmap = {}
    tracemalloc.start()
    for n in range(10, 27):
        tracemalloc.reset_peak()
        base = tracemalloc.get_traced_memory()[0]
        psi = np.zeros(1 << n, dtype=np.complex128)
        psi[0] = 1.0
        reps = 3 if n <= 20 else 1
        ts = []
        for _ in range(reps):
            t0 = time.perf_counter()
            random_layer(psi, n, rng)
            ts.append(time.perf_counter() - t0)
        peak = tracemalloc.get_traced_memory()[1] - base
        cmap[n] = {"state_bytes": 16 * 2**n, "peak_bytes": int(peak), "peak_over_state": peak / (16 * 2**n),
                   "seconds_per_layer": float(np.median(ts)), "seconds_per_gate": float(np.median(ts)) / n,
                   "norm_minus_1": float(np.vdot(psi, psi).real - 1)}
        del psi
    tracemalloc.stop()
    ns = np.array(sorted(cmap))
    tg = np.array([cmap[n]["seconds_per_gate"] for n in ns])
    sel = ns >= 18
    slope, icpt = np.polyfit(ns[sel], np.log2(tg[sel]), 1)
    A = float(np.median(tg[sel] / 2.0 ** ns[sel]))           # seconds per gate per amplitude, 2^n law with slope 1
    extra = {}
    for n in (50, 4000, 4099):
        log10_bytes = math.log10(16) + n * math.log10(2)
        log10_layer_s = math.log10(A * n) + n * math.log10(2)
        extra[n] = {"log10_state_bytes": log10_bytes, "log10_seconds_per_layer": log10_layer_s,
                    "log10_years_per_layer": log10_layer_s - math.log10(3.15576e7)}
    out["cost_map"] = {"per_n": cmap, "fit_log2_seconds_per_gate_vs_n": {"n_range": [18, 26], "slope": slope, "intercept": icpt},
                       "seconds_per_gate_per_amplitude": A, "extrapolation": extra,
                       "note": "wall times measured single-threaded on a shared 4-core machine; memory = 16 bytes per amplitude (complex128)"}
    print("  cost map (one random layer):")
    for n in ns:
        print(f"     n = {n:>2}: state {cmap[n]['state_bytes'] / 2**20:10.3f} MiB, measured peak {cmap[n]['peak_bytes'] / 2**20:10.3f} MiB, "
              f"{cmap[n]['seconds_per_layer']:.4f} s per layer")
    info("2^n law: slope of log2(seconds per gate) against n for n = 18..26 (1 for the 2^n law)", f"{slope:.3f}")
    info("extrapolated state memory, n = 50", f"{16 * 2**50 / 1e15:.1f} PB (10^{extra[50]['log10_state_bytes']:.2f} bytes), one layer about "
         f"10^{extra[50]['log10_seconds_per_layer']:.1f} s")
    info("extrapolated state memory, n = 4000 and 4099 (a 2048-bit RSA modulus, 2n + 3)", f"10^{extra[4000]['log10_state_bytes']:.1f} and "
         f"10^{extra[4099]['log10_state_bytes']:.1f} bytes")
    check_true(f"memory law: measured peak = 16 * 2^n bytes plus a bounded buffer; at n = 26 the ratio is {cmap[26]['peak_over_state']:.4f} (<= 1.05)",
               cmap[26]["peak_over_state"] <= 1.05 and all(cmap[n]["peak_bytes"] >= cmap[n]["state_bytes"] for n in ns))
    check_true("every random layer preserved the norm to 1e-10 (n = 10..26)", all(abs(cmap[n]["norm_minus_1"]) < 1e-10 for n in ns))
    out["seconds"] = time.perf_counter() - t_start
    out["peak_rss_gb_so_far"] = peak_rss_gb()
    info("B4 runtime, s", f"{out['seconds']:.1f}")
    R["B4"] = out


# ---------------------------------------------------------------------------------------------------------------------------------
def to_jsonable(o):
    if isinstance(o, dict):
        return {str(k): to_jsonable(v) for k, v in o.items()}
    if isinstance(o, (list, tuple)):
        return [to_jsonable(v) for v in o]
    if isinstance(o, np.ndarray):
        return [to_jsonable(v) for v in o.tolist()]
    if isinstance(o, (np.bool_, bool)):
        return bool(o)
    if isinstance(o, (np.integer,)):
        return int(o)
    if isinstance(o, (np.floating, float)):
        return float(o)
    return o


if __name__ == "__main__":
    only = sys.argv[sys.argv.index("--only") + 1] if "--only" in sys.argv else None
    t_all = time.perf_counter()
    for name, fn in (("B1", b1), ("B2", b2), ("B3", b3), ("B4", b4)):
        if only in (None, name):
            fn()
    total = time.perf_counter() - t_all
    info("total runtime, s", f"{total:.1f}")
    info("peak resident memory, GB", f"{peak_rss_gb():.2f}")
    if only is None:
        R["meta"] = {"script": "docs/simulation/hosted_benchmarks.py", "run_date_utc": time.strftime("%Y-%m-%d", time.gmtime()),
                     "python": platform.python_version(), "numpy": np.__version__,
                     "scipy": scipy.__version__, "blas_threads": os.environ.get("OPENBLAS_NUM_THREADS"), "cpu_count": os.cpu_count(),
                     "total_seconds": total, "peak_rss_gb": peak_rss_gb(), "checks_passed": int(sum(results)), "checks_total": len(results)}
        R["checks"] = CHECKS
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(json.dumps(to_jsonable(R), indent=1) + "\n")
        print(f"wrote {OUT}")
    print(f"\n{sum(results)} of {len(results)} checks passed")
    raise SystemExit(0 if all(results) else 1)
