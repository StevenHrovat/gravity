"""Join-loss round: third-layer (refute-only) check. CPU, seconds, no new simulation.

Part A [classical formulas; numerical]: 2D SU(2) on a torus, solved by characters.
    Z_e0(A) = sum over odd n of r_n^A, Z_e1(A) = sum over even n of r_n^A, r_n = I_n(beta)/I_1(beta) (n = 2j + 1),
    continuum: r_n = exp(-(n^2 - 1)/8) (area in units of the leading string tension 3/8).
    Checks the Lean bounds of JoinLoss.lean (joinLoss_bounds) at the self-dual area A_h:
        -(t1(a) + t1(b)) <= l(a, b) <= t0(a) + t0(b),  t_e(A) = log(Z_e(A) / top_e^A),
    and whether the neutral tail alone clears the three-box condition of ymOneBox_torus: log mu4 + 4 t0 < 3 log(1+sqrt2).

Part B [numerical, refute-only]: 4D SU(2), saved small-torus data (ONEBOX-CHECK.md 8 and 9,
    w2/runs/smalltorus_result.json). The torus L^3 x 2L doubles a direction of the twist plane (0, k), so
        l(L) = 2 F_e(L^4) - F_e(L^3 x 2L)
    is exactly the transfer-matrix join loss of two L^4 boxes. Also the neutral join excess phi0 = 2c_lb (measured
    there, = log Z0(L)^2/Z0(2L)) and phi1 = phi0 - l (Lean: joinLoss_eq).
    Error bar = max(statistical, resolution floor 1) (attempts/RULES.md, last section; floor 1 for log-ratios as in
    ONEBOX-CHECK.md 8.3). Refuted at threshold theta if l - 1.645 * sigma > theta.
    Thresholds per join (Lean: ymOneBox_of_split): three boxes (3 log(1+sqrt2) - log mu4)/2 = 0.366;
    four boxes (4 log(1+sqrt2) - log mu4)/3 = 0.538.
"""
import json
import os

import numpy as np
from scipy.special import iv

HERE = os.path.dirname(os.path.abspath(__file__))
LOG_MU4 = np.log(6.77)
S = np.log(1 + np.sqrt(2))
TH3 = (3 * S - LOG_MU4) / 2
TH4 = (4 * S - LOG_MU4) / 3
NMAX = 60

print(f"thresholds per join: three boxes {TH3:.4f}, four boxes {TH4:.4f} (iterated form k(F-2C): three {S - LOG_MU4/3:.4f})")

# ---------------------------------------------------------------- Part A
print("\n== Part A: 2D SU(2), the sector bounds of joinLoss_bounds at the self-dual area [classical formulas, numerical]")


def eig(beta):
    n = np.arange(1, NMAX + 1)
    if beta == "continuum":
        r = np.exp(-(n * n - 1) / 8.0)
    else:
        r = iv(n, beta) / iv(1, beta)
    return n, r


def sec(beta, A):
    n, r = eig(beta)
    w = r ** A
    z0, z1 = w[n % 2 == 1].sum(), w[n % 2 == 0].sum()
    top0, top1 = r[0], r[1]  # n = 1 (j = 0) and n = 2 (j = 1/2)
    return z0, z1, np.log(z0 / top0 ** A), np.log(z1 / top1 ** A)


def fe(beta, A):
    z0, z1, _, _ = sec(beta, A)
    return np.log(z0 / z1)


def solve(beta, target):
    lo, hi = 1e-6, 400.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if fe(beta, mid) < target:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


ok_all = True
for beta in (1.0, 2.3, 4.0, 8.0, 32.0, "continuum"):
    ah = solve(beta, S)
    _, _, t0, t1 = sec(beta, ah)
    rows = []
    for (a, b) in ((1, 1), (2, 1), (2, 2)):
        A, B = a * ah, b * ah
        l = fe(beta, A) + fe(beta, B) - fe(beta, A + B)
        _, _, t0a, t1a = sec(beta, A)
        _, _, t0b, t1b = sec(beta, B)
        lo, hi = -(t1a + t1b), t0a + t0b
        ok = lo - 1e-12 <= l <= hi + 1e-12
        ok_all &= ok
        rows.append(f"({a},{b}) A_h: l={l:+.4f} in [{lo:+.4f}, {hi:+.4f}] {'ok' if ok else 'VIOLATED'}")
    clears = LOG_MU4 + 4 * t0 < 3 * S
    print(f"beta={beta!s:>9}  A_h={ah:.4f}  neutral tail t0(A_h)={t0:.4f}  charged tail t1(A_h)={t1:.4f}  "
          f"tail-only bound 2 t0={2*t0:.4f}  ymOneBox_torus condition (t0 < {(3*S-LOG_MU4)/4:.4f}): {clears}")
    for r_ in rows:
        print("    " + r_)
print(f"Lean bounds hold at every point checked: {ok_all}")

# ---------------------------------------------------------------- Part B
print("\n== Part B: 4D SU(2), join loss from the saved small-torus data [numerical, refute-only]")
path = os.path.join(HERE, "..", "mass-gap", "weak-coupling", "proof-phase", "c9a-crossover", "w2", "runs",
                    "smalltorus_result.json")
d = json.load(open(path))


def fe_r(r):
    return np.log((1 + r) / (1 - r))


for key in ("2.3_2", "2.3_4", "2.3_6", "3.5_2", "3.5_4", "3.5_6"):
    e = d[key]
    rL, r2 = e["r_L"], e["r_2L"]
    F1, sF1 = e["F_e"], e["sig_F_e"]
    F2 = fe_r(r2)
    sF2 = 2 * r2 / (1 - r2 ** 2) * e["sig_log_r_2L"]
    l = 2 * F1 - F2
    sl = np.hypot(2 * sF1, sF2)
    sig = max(sl, 1.0)
    phi0 = e["two_c_lb"]
    phi1 = phi0 - l
    v3 = "refuted" if l - 1.645 * sig > TH3 else "not refuted"
    v4 = "refuted" if l - 1.645 * sig > TH4 else "not refuted"
    v3s = "refuted" if l - 1.645 * sl > TH3 else "not refuted"
    print(f"beta={e['beta']} L={e['L']}: F_e(L)={F1:.3f}+-{sF1:.3f}  F_e(L^3x2L)={F2:.3f}+-{sF2:.3f}  "
          f"l={l:+.3f}+-{sl:.3f} (stat)  phi0=2c_lb={phi0:.3f}  phi1={phi1:.3f}")
    print(f"    three-box threshold {TH3:.3f}: {v3} (floor 1); {v3s} (stat only).  four-box {TH4:.3f}: {v4} (floor 1)")

# ---------------------------------------------------------------- projection for a new run (not run)
print("\n== Projection for a new run at L = 8 (not run)")
# sweep cost scales ~ volume; ONEBOX-CHECK.md 8.6: 6^4 snake 17.9 ms, 6^3x12 snake 26.7 ms per sweep
ms8 = 17.9 * (8 / 6) ** 4
ms8x2 = 26.7 * (8 / 6) ** 4
sweeps = 2200
sec_ = 64 * sweeps * (ms8 + ms8x2) / 1000
print(f"one beta, L = 8, snake on 8^4 and 8^3x16 (64 ensembles each, 2200 sweeps): {sec_/3600:.1f} h raw, "
      f"central x1.33 = {sec_*1.33/3600:.1f} h, band {sec_*0.9/3600:.1f} to {sec_*1.9/3600:.1f} h  -> over 1 CPU-hour, not run")

# ---------------------------------------------------------------- Part C
print("\n== Part C: 2D SU(2) continuum cylinder, the boundary-uniform electric factor (JoinLossSlab.lean) [classical, numerical]")
# Slab = cylinder of area A between two boundary holonomies with class angles th1, th2 (the end-face outside).
# Heat kernel K_A(th1, th2) = sum_n chi_n(th1) chi_n(th2) exp(-(n^2-1) A/8), chi_n(th) = sin(n th)/sin(th), n = 2j + 1.
# Centre twist of a face: th -> pi - th (holonomy -> -holonomy); chi_n(pi - th) = (-1)^(n-1) chi_n(th).
M = 400
th = (np.arange(M) + 0.5) * np.pi / M
nn = np.arange(1, 81)
chi = np.sin(np.outer(nn, th)) / np.sin(th)[None, :]


def kern(A):
    w = np.exp(-(nn * nn - 1) * A / 8.0)
    return (chi * w[:, None]).T @ chi  # K[i, k] = K_A(th_i, th_k)


def rho_unif(A):
    K = kern(A)
    Kt = K[:, ::-1]  # far face twisted: th_k -> pi - th_k
    assert K.min() > 0, "heat kernel must be positive"
    return np.max(np.abs(K - Kt) / (K + Kt))


def c_min(A):
    K = kern(A)
    return np.min(K[:, ::-1] / K)


ok = True
for A1, A2 in ((2.0, 2.0), (3.0, 2.0), (4.0, 4.0), (6.0, 3.0)):
    r12, r1, r2 = rho_unif(A1 + A2), rho_unif(A1), rho_unif(A2)
    ok &= r12 <= r1 * r2 * (1 + 1e-9)
    print(f"  rho({A1}+{A2}) = {r12:.5f} <= rho({A1}) rho({A2}) = {r1 * r2:.5f}: {r12 <= r1 * r2 * (1 + 1e-9)}")
print(f"  elec_submul holds at every pair checked: {ok}")
lo, hi = 0.1, 60.0
for _ in range(80):
    mid = 0.5 * (lo + hi)
    if rho_unif(mid) > np.sqrt(2) - 1:
        lo = mid
    else:
        hi = mid
ahu = 0.5 * (lo + hi)
ah_t = solve("continuum", S)
print(f"  uniform hand-over area (pointwise c_min = sqrt2 - 1): {ahu:.4f}  (torus hand-over {ah_t:.4f}, ratio {ahu/ah_t:.3f}); "
      f"c_min there {c_min(ahu):.4f}")
F3 = -np.log(rho_unif(3 * ahu))
print(f"  three uniform hand-over slabs: F_e^unif = {F3:.4f} >= 3 x 0.8814 = {3*S:.4f} (zero loss), floor log mu4 = {LOG_MU4:.4f}")
lo, hi = 0.1, 60.0
for _ in range(80):
    mid = 0.5 * (lo + hi)
    if rho_unif(mid) > 1 / 6.77:
        lo = mid
    else:
        hi = mid
ao1u = 0.5 * (lo + hi)
print(f"  uniform O1 area (rho_unif = 1/mu4): {ao1u:.4f} = {ao1u/ahu:.3f} uniform hand-over areas "
      f"(torus O1 area {solve('continuum', LOG_MU4):.4f})")
