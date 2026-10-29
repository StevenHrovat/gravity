"""Bell tests under Dualism: the checks behind docs/bell/bell.tex.

Needs numpy and scipy (scipy only for the linear programme of [B5]). Runs in a few seconds. Every printed line is a check with its
expected value; the last line counts them.

The question (the first author, 2026-10-29 09:24Z): did the Bell experiments of the 2022 Nobel prize "actually not violate Bell
inequality under Dualism"? A Duality whose two halves each decide on their own setting and a shared hidden state is a local model; the
checks below say what each other reading of the Duality has to give up to reproduce what the laboratories measured.

  [B1] isolated halves (gravity#17's gateModel): S <= 2 over all 16 deterministic strategies
  [B2] full reach (Refute.lean's rfFullReachGate): S reaches 4, and the S = 4 model signals Alice's setting to Bob
  [B3] no-signalling alone does not stop at quantum mechanics: the PR box reaches 4 with uniform marginals
  [B4] the singlet reaches 2*sqrt(2) (Tsirelson) with uniform marginals
  [B5] superdeterminism: the least measurement dependence M (Hall 2010) a local deterministic model needs to reach S is (S - 2)/3
  [B6] the measured S values of the three loophole-free CHSH tests lie above 2
  [B7] gravity-mediated entanglement (Bose et al. 2017 geometry): coherent mediator entangles, recorded mediator does not
  [B8] Kerr: the horizon is set by the irreducible mass alone, r+ = 2 M_irr^2 / M; the spin's share is up to 1 - 1/sqrt(2)
"""

import itertools

import numpy as np

results = []


def check(label, got, want, tol=1e-6):
    ok = abs(got - want) <= tol
    print(f"{'OK  ' if ok else 'FAIL'} {label}: {got:.6f} (expected {want:.6f})")
    results.append(ok)


def check_true(label, cond):
    print(f"{'OK  ' if cond else 'FAIL'} {label}")
    results.append(bool(cond))


def pm(b):
    return 1 if b else -1


SETTINGS = [(0, 0), (0, 1), (1, 0), (1, 1)]
SIGN = {(0, 0): 1, (0, 1): 1, (1, 0): 1, (1, 1): -1}

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B1] Isolated halves: each outcome depends on its own setting and the shared hidden state only")
# A deterministic local strategy is (a0, a1, b0, b1); every local model is a mixture of these 16 (Fine 1982), so the maximum over
# them is the maximum over all local models with measurement independence.
LOCAL = list(itertools.product([0, 1], repeat=4))


def s_local(lam):
    a0, a1, b0, b1 = lam
    a, b = (a0, a1), (b0, b1)
    return sum(SIGN[(x, y)] * pm(a[x]) * pm(b[y]) for x, y in SETTINGS)


check("largest |S| over the 16 local deterministic strategies (gate_obeys_chsh)", max(abs(s_local(l)) for l in LOCAL), 2)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B2] Full reach: each half reads both settings (Axiom 1's 'full reach over the act')")
# Each half's outcome is a function of (x, y): 16 functions per side, 256 strategies.
FUNCS = list(itertools.product([0, 1], repeat=4))  # f[(2x + y)]


def s_full(fa, fb):
    return sum(SIGN[(x, y)] * pm(fa[2 * x + y]) * pm(fb[2 * x + y]) for x, y in SETTINGS)


check("largest S over the 256 full-reach strategies", max(s_full(fa, fb) for fa in FUNCS for fb in FUNCS), 4)
# Refute.lean's rfFullReachGate: A always passes, B refuses exactly when x and y are both 1.
fa = tuple(1 for x, y in SETTINGS)
fb = tuple(0 if (x and y) else 1 for x, y in SETTINGS)
check("S of rfFullReachGate (rf_full_reach_reaches_four)", s_full(fa, fb), 4)
# Bob's outcome at y = 1 as a function of Alice's setting x: it changes, so Bob reads Alice's setting from his own outcome.
check("Bob's outcome at y=1 differs between x=0 and x=1 (the S = 4 gate signals)", abs(fb[2 * 0 + 1] - fb[2 * 1 + 1]), 1)
# Every deterministic full-reach strategy that reaches S > 2 is non-local: Alice's outcome depends on y or Bob's on x. A deterministic
# outcome that depends on the far setting is a signal, so deterministic + no-signalling is local and stays at 2.
def local_strategy(fa, fb):
    return fa[0] == fa[1] and fa[2] == fa[3] and fb[0] == fb[2] and fb[1] == fb[3]


check_true("every deterministic full-reach strategy with S > 2 lets one side's outcome depend on the other side's setting",
           all(not local_strategy(fa, fb) for fa in FUNCS for fb in FUNCS if s_full(fa, fb) > 2))

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B3] No-signalling alone allows S = 4 (Popescu and Rohrlich 1994)")
# PR box: P(a, b | x, y) = 1/2 if a XOR b = x AND y, else 0.
def pr(a, b, x, y):
    return 0.5 if (a ^ b) == (x & y) else 0.0


s_pr = sum(SIGN[(x, y)] * sum(pm(a) * pm(b) * pr(a, b, x, y) for a in (0, 1) for b in (0, 1)) for x, y in SETTINGS)
check("S of the PR box", s_pr, 4)
marg = [sum(pr(1, b, x, y) for b in (0, 1)) for x, y in SETTINGS] + [sum(pr(a, 1, x, y) for a in (0, 1)) for x, y in SETTINGS]
check("largest deviation of a PR-box marginal from 1/2 (no signalling)", max(abs(m - 0.5) for m in marg), 0)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B4] Quantum mechanics: the singlet at the optimal angles reaches Tsirelson's bound 2*sqrt(2)")
X = np.array([[0, 1], [1, 0]], dtype=complex)
Z = np.diag([1.0, -1.0]).astype(complex)
singlet = np.array([0, 1, -1, 0], dtype=complex) / np.sqrt(2)
A_OBS = [Z, X]
B_OBS = [-(Z + X) / np.sqrt(2), -(Z - X) / np.sqrt(2)]


def expect(op, psi):
    return float(np.real(np.conj(psi) @ op @ psi))


s_q = sum(SIGN[(x, y)] * expect(np.kron(A_OBS[x], B_OBS[y]), singlet) for x, y in SETTINGS)
check("S of the singlet", s_q, 2 * np.sqrt(2))
marg_q = [expect(np.kron(A_OBS[x], np.eye(2)), singlet) for x in (0, 1)] + [expect(np.kron(np.eye(2), B_OBS[y]), singlet) for y in (0, 1)]
check("largest single-side expectation (no signalling)", max(abs(m) for m in marg_q), 0)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B5] Superdeterminism: how much the hidden state must depend on the settings")
# A local deterministic model with measurement dependence: a distribution p(lam | x, y) over the 16 strategies for each setting pair.
# Hall (2010): M = max over setting pairs of sum_lam |p(lam|x,y) - p(lam|x',y')|, from 0 (independent) to 2 (fully dependent).
# Linear programme: the least M for which a model reaches CHSH value S, and the least M that reproduces the singlet's full CHSH
# statistics (every correlator +-1/sqrt(2), every marginal 0).
try:
    from scipy.optimize import linprog
except ImportError:  # pragma: no cover
    linprog = None


def least_m(target, full):
    pairs = list(itertools.combinations(range(4), 2))
    n_p, n_u = 64, len(pairs) * 16
    n = n_p + n_u + 1
    c = np.zeros(n)
    c[-1] = 1
    a_eq, b_eq, a_ub, b_ub = [], [], [], []
    for s in range(4):
        r = np.zeros(n)
        r[s * 16:(s + 1) * 16] = 1
        a_eq.append(r)
        b_eq.append(1)
    if full:
        for s, (x, y) in enumerate(SETTINGS):
            r, ra, rb = np.zeros(n), np.zeros(n), np.zeros(n)
            for li, lam in enumerate(LOCAL):
                r[s * 16 + li] = pm(lam[x]) * pm(lam[2 + y])
                ra[s * 16 + li] = pm(lam[x])
                rb[s * 16 + li] = pm(lam[2 + y])
            a_eq += [r, ra, rb]
            b_eq += [SIGN[(x, y)] * target / 4, 0, 0]
    else:
        r = np.zeros(n)
        for s, (x, y) in enumerate(SETTINGS):
            for li, lam in enumerate(LOCAL):
                r[s * 16 + li] = -SIGN[(x, y)] * pm(lam[x]) * pm(lam[2 + y])
        a_ub.append(r)
        b_ub.append(-target)
    for k, (s1, s2) in enumerate(pairs):
        for li in range(16):
            ui = n_p + k * 16 + li
            for sg in (1, -1):
                r = np.zeros(n)
                r[s1 * 16 + li], r[s2 * 16 + li], r[ui] = sg, -sg, -1
                a_ub.append(r)
                b_ub.append(0)
        r = np.zeros(n)
        r[n_p + k * 16:n_p + (k + 1) * 16] = 1
        r[-1] = -1
        a_ub.append(r)
        b_ub.append(0)
    res = linprog(c, A_ub=np.array(a_ub), b_ub=b_ub, A_eq=np.array(a_eq), b_eq=b_eq, bounds=[(0, None)] * n, method="highs")
    return res.fun


if linprog is None:
    print("SKIP [B5] needs scipy")
else:
    for s_val, name in [(2.0747, "ETH Zurich 2023"), (2.22, "Munich 2017"), (2.42, "Delft 2015"), (2 * np.sqrt(2), "Tsirelson"),
                        (4.0, "algebraic maximum")]:
        check(f"least M to reach S = {s_val:.4f} ({name}), equal to (S - 2)/3", least_m(s_val, False), (s_val - 2) / 3, tol=1e-6)
    check("least M to reproduce the singlet's full CHSH statistics, equal to (2*sqrt(2) - 2)/3", least_m(2 * np.sqrt(2), True),
          (2 * np.sqrt(2) - 2) / 3, tol=1e-6)
    check("as a share of the maximum M = 2 (Hall 2010 reports about 14% for the singlet)", least_m(2 * np.sqrt(2), True) / 2,
          (np.sqrt(2) - 1) / 3, tol=1e-6)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B6] What the laboratories measured: CHSH values of the loophole-free tests, distance above the local bound 2")
# Published values (CHSH form). Giustina et al. 2015 and Shalm et al. 2015 used the CH/Eberhard form and report p-values instead.
MEASURED = [
    ("Hensen et al. 2015, electron spins, 1.3 km", 2.42, 0.20),
    ("Rosenfeld et al. 2017, rubidium atoms, 398 m", 2.22, 0.033),
    ("Storz et al. 2023, superconducting qubits, 30 m", 2.0747, 0.0033),
]
for name, s_val, sd in MEASURED:
    z = (s_val - 2) / sd
    print(f"     {name}: S = {s_val} +- {sd}, (S - 2)/sigma = {z:.1f}")
    check_true(f"{name}: S above 2 and below 2*sqrt(2)", 2 < s_val < 2 * np.sqrt(2))

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B7] Gravity-mediated entanglement in the Bose et al. (2017) geometry")
# Two masses m, each in a superposition of two positions Delta_x apart, centres d apart, on one line. The four branch distances are
# d (LL, RR), d - Delta_x (inner pair), d + Delta_x (outer pair). A quantum (coherent) field gives each branch the phase
# G m^2 t / (hbar r); the entangling phase is the combination that no local operation removes.
G, HBAR = 6.67430e-11, 1.054571817e-34
m, d, dx = 1e-14, 450e-6, 250e-6
r = {(0, 0): d, (1, 1): d, (1, 0): d - dx, (0, 1): d + dx}  # (position of mass 1, position of mass 2); 1 = towards the other mass
rate = {k: G * m * m / (HBAR * v) for k, v in r.items()}
dphi_rate = rate[(1, 0)] + rate[(0, 1)] - rate[(0, 0)] - rate[(1, 1)]
print(f"     entangling phase rate: {dphi_rate:.4f} rad/s; dominant inner-pair rate G m^2/(hbar (d - dx)): {rate[(1, 0)]:.4f} rad/s")


def negativity(rho):
    pt = rho.reshape(2, 2, 2, 2).transpose(0, 3, 2, 1).reshape(4, 4)
    ev = np.linalg.eigvalsh(pt)
    return float(-ev[ev < 0].sum())


def state_at(t):
    psi = np.array([np.exp(1j * rate[(i, j)] * t) for i in (0, 1) for j in (0, 1)]) / 2
    return np.outer(psi, psi.conj())


# For the branch phases above, the negativity is |sin(dphi / 2)| / 2: 0.5 when the entangling phase reaches pi.
t_pi = np.pi / dphi_rate
t_one = 1.0 / dphi_rate
print(f"     time to an entangling phase of 1 rad: {t_one:.1f} s; of pi: {t_pi:.1f} s")
check(f"negativity with a coherent mediator at t = {t_one:.1f} s, equal to sin(1/2)/2", negativity(state_at(t_one)), np.sin(0.5) / 2,
      tol=1e-9)
check(f"negativity with a coherent mediator at t = {t_pi:.1f} s (maximal)", negativity(state_at(t_pi)), 0.5, tol=1e-9)
# A mediator held in full by two witnesses is recorded: the branch is dephased in the position basis.
rho_rec = np.diag(np.diag(state_at(t_pi)))
check("negativity with a recorded (classical) mediator at the same time", negativity(rho_rec), 0, tol=1e-12)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B8] Kerr: the horizon of a spinning black hole is set by its irreducible mass")
# Units G = c = 1, mass M = 1, spin a = J / M^2 in [0, 1]. Kerr (1963): outer horizon r+ = M (1 + sqrt(1 - a^2)).
# Christodoulou (1970): irreducible mass M_irr^2 = A / (16 pi), with horizon area A = 4 pi (r+^2 + a^2 M^2); the rest of M is rotational
# energy that can be taken out (Penrose; Blandford and Znajek) without shrinking the area.
M = 1.0
worst = 0.0
for a in np.linspace(0, 1, 11):
    r_plus = M * (1 + np.sqrt(1 - a * a))
    area = 4 * np.pi * (r_plus ** 2 + (a * M) ** 2)
    m_irr = np.sqrt(area / (16 * np.pi))
    worst = max(worst, abs(r_plus - 2 * m_irr ** 2 / M))
check("largest |r+ - 2 M_irr^2 / M| over spins 0, 0.1, ..., 1 (the horizon depends on the spin only through M_irr)", worst, 0, tol=1e-12)
check("horizon radius at a = 0 (Schwarzschild, 2M)", M * (1 + np.sqrt(1 - 0.0)), 2.0)
check("horizon radius at a = 1 (extremal Kerr, M)", M * (1 + np.sqrt(1 - 1.0)), 1.0)
m_irr_ext = np.sqrt(4 * np.pi * (1.0 + 1.0) / (16 * np.pi))
check("share of the mass that is rotational at a = 1, 1 - M_irr/M", 1 - m_irr_ext / M, 1 - 1 / np.sqrt(2))

print(f"\n{sum(results)} of {len(results)} checks passed")
