"""GUID v5: Quantum Gravity. Every number the paper uses, computed from named inputs.

Run: python3 docs/quantum-gravity/checks.py   (numpy, scipy, sympy). Each check prints OK or FAIL; the last line counts them.
The holographic-code assembly of Section 9 is a separate script, docs/qg-verdict/assembly.py (18 of 18).

  [Q1]  Planck units; the only energy g, h and c form is g h / c, and it is 4 pi^2 k T_Unruh; Unruh and Hawking temperatures;
        Bekenstein-Hawking entropy; the entropy density per area that Jacobson's argument turns into G; the size of the quantum
        term of the effective-field-theory Newtonian potential at 1 m
  [Q2]  the lapse: gravitational redshift over the Pound-Rebka tower and over 33 cm; the lapse vanishes at the horizon
  [Q3]  no-cloning and no-broadcasting: two states can be copied by one process only if their overlap is 0 or 1; a copier in a
        fixed basis broadcasts exactly the states diagonal in that basis
  [Q4]  a classical (recorded) mediator cannot entangle: 300 random local couplings through a mediator that is dephased after every
        coupling never leave the two systems entangled; the same couplings with a coherent mediator do
  [Q5]  gravitationally mediated entanglement in the geometry of Bose et al. (2017): phases, the entangling rate, the negativity
        with a coherent and with a recorded field
  [Q6]  universality of free fall: the MICROSCOPE bound on a scalar that sets alpha; gravity cannot weigh only the Higgs share
  [Q7]  light bending: Brans-Dicke gamma and Cassini's bound on omega
  [Q8]  polarisations of a massless spin-2 field and Weyl components in D dimensions (2 and 10 in 3+1, 0 and 0 in 2+1)
  [Q9]  single gravitons: the Planck-scale horizon threshold of one quantum, a LIGO-band graviton against it, quanta in GW150914
  [Q10] Kerr black holes: horizon, ergosphere, irreducible mass (Christodoulou), 29% extractable, accretion efficiency 5.7% to 42.3%
  [Q11] Hawking radiation of a solar-mass hole against the cosmic microwave background; evaporation time
  [Q12] a flat Friedmann universe sits at its own Schwarzschild threshold at every epoch: 2 G M_H / c^2 = c / H
  [Q13] inflation: e-folds that flatten an order-one curvature; de Sitter floor of the Hubble rate; onset of acceleration
  [Q14] primordial tensor modes: P_t = 16 G hbar H^2 / (pi c^5) vanishes with hbar; the BICEP/Keck bound in inflation energy;
        Starobinsky's r and the consistency relation n_t = -r/8
  [Q15] dark matter as neutrinos: cosmological density for the allowed mass sum, Pauli (Tremaine-Gunn) bound for a dwarf galaxy,
        relic and stellar neutrinos against the Galactic escape speed; the baryon fraction
  [Q16] alpha as the self-interaction strength of charge: Schwinger's a_e = alpha/2pi; alpha as the ratio of the electron's lengths;
        gravity against electromagnetism in hydrogen; 1/alpha at the Planck energy (Standard Model, one loop)
  [Q17] the speed of gravitational waves from GW170817 and GRB 170817A
"""

import math

import numpy as np
import sympy as sp

results = []


def check(label, got, want, rtol=1e-6, atol=0.0):
    got, want = float(got), float(want)
    ok = abs(got - want) <= max(atol, rtol * abs(want))
    print(f"{'OK  ' if ok else 'FAIL'} {label}: {got:.6g} (expected {want:.6g})")
    results.append(ok)


def check_true(label, cond):
    print(f"{'OK  ' if cond else 'FAIL'} {label}")
    results.append(bool(cond))


# Constants: SI 2019 exact values, CODATA 2018, IAU nominal values.
h = 6.62607015e-34          # J s
hbar = h / (2 * math.pi)
c = 299792458.0             # m/s
G = 6.67430e-11             # m^3 kg^-1 s^-2
kB = 1.380649e-23           # J/K
eV = 1.602176634e-19        # J
e_charge = 1.602176634e-19  # C
eps0 = 8.8541878128e-12     # F/m
m_e = 9.1093837015e-31      # kg
m_p = 1.67262192369e-27     # kg
alpha = 7.2973525693e-3
M_sun = 1.98847e30          # kg
year = 3.15576e7            # s (Julian)
pc = 3.0856775814913673e16  # m
Mpc = 1e6 * pc
L_P = math.sqrt(hbar * G / c**3)
t_P = L_P / c
E_P = math.sqrt(hbar * c**5 / G)
GeV = 1e9 * eV

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[Q1] Planck units, the existence energy g h / c, Unruh, Hawking, Bekenstein-Hawking, Jacobson's entropy density")
check("Planck length in m", L_P, 1.616255e-35, rtol=1e-5)
check("Planck energy in GeV", E_P / GeV, 1.220890e19, rtol=1e-5)
a, b, k = sp.symbols("a b k")
# dimensions (M, L, T): g = L T^-2, h = M L^2 T^-1, c = L T^-1; energy = M L^2 T^-2
sol = sp.solve([sp.Eq(b, 1), sp.Eq(a + 2 * b + k, 2), sp.Eq(-2 * a - b - k, -2)], [a, b, k], dict=True)
check_true("g^a h^b c^k is an energy only for (a, b, k) = (1, 1, -1)", sol == [{a: 1, b: 1, k: -1}])
g0 = 9.80665
E_ex = g0 * h / c
kT_U = hbar * g0 / (2 * math.pi * c)
check("(g h / c) / (k T_Unruh) = 4 pi^2", E_ex / kT_U, 4 * math.pi**2)
check("Unruh temperature at standard gravity, K", kT_U / kB, 3.98e-20, rtol=5e-3)
T_H_sun = hbar * c**3 / (8 * math.pi * G * M_sun * kB)
check("Hawking temperature of a solar-mass black hole, K", T_H_sun, 6.17e-8, rtol=5e-3)
kappa = c**4 / (4 * G * M_sun)   # surface gravity of a Schwarzschild hole
check("Hawking temperature = Unruh temperature at the surface gravity c^4 / 4GM", hbar * kappa / (2 * math.pi * c * kB), T_H_sun)
S_sun = 4 * math.pi * G * M_sun**2 / (hbar * c)   # S / k = A / (4 L_P^2)
check("Bekenstein-Hawking entropy of a solar-mass hole, in units of k", S_sun, 1.05e77, rtol=1e-2)
eft_q = 41 / (10 * math.pi) * G * hbar / (1.0**2 * c**3)
check("quantum term of the EFT Newtonian potential at r = 1 m, (41/10pi) G hbar / (r^2 c^3)", eft_q, 3.41e-70, rtol=1e-2)
eta_J = 1 / (4 * L_P**2)
check("Jacobson: entropy per area eta = 1/(4 L_P^2) returns G = c^3 / (4 hbar eta)", c**3 / (4 * hbar * eta_J), G)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[Q2] The lapse N = sqrt(1 + 2 Phi / c^2): the rate at which a clock asserts its existence")
check("fractional redshift over the 22.5 m Pound-Rebka tower, g h / c^2", g0 * 22.5 / c**2, 2.455e-15, rtol=1e-3)
check("fractional rate difference of two clocks 33 cm apart (Chou et al. 2010)", g0 * 0.33 / c**2, 3.60e-17, rtol=1e-2)
r_s = 2 * G * M_sun / c**2
rs = np.array([4, 2, 1.1, 1.01, 1.0001]) * r_s
lapse = np.sqrt(1 - r_s / rs)
check_true("the Schwarzschild lapse sqrt(1 - r_s/r) falls monotonically to 0 at the horizon",
           all(np.diff(lapse) < 0) and lapse[-1] < 0.011)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[Q3] No-cloning and no-broadcasting: what two witnesses can each hold in full")
for s in (0.0, 1.0, 1 / math.sqrt(2), 0.3):
    check_true(f"overlap {s:.3f}: one unitary copies both states only if s = s^2 -> {'allowed' if s in (0.0, 1.0) else 'forbidden'}",
               (abs(s - s**2) < 1e-12) == (s in (0.0, 1.0)))
CNOT = np.array([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]], dtype=complex)


def broadcast(rho):
    """Copy a qubit in the computational basis onto a blank qubit (CNOT); return both reduced states."""
    blank = np.array([[1, 0], [0, 0]], dtype=complex)
    out = CNOT @ np.kron(rho, blank) @ CNOT.conj().T
    t = out.reshape(2, 2, 2, 2)
    return np.einsum("ijkj->ik", t), np.einsum("ijil->jl", t)


rho_diag = np.diag([0.7, 0.3]).astype(complex)
plus = np.array([[0.5, 0.5], [0.5, 0.5]], dtype=complex)
r1, r2 = broadcast(rho_diag)
check_true("a state diagonal in the copier's basis is broadcast: both readers hold it in full", np.allclose(r1, rho_diag) and np.allclose(r2, rho_diag))
r1, r2 = broadcast(plus)
check_true("|+><+| (not diagonal) is not: each reader holds I/2, the coherence is gone", np.allclose(r1, np.eye(2) / 2) and np.allclose(r2, np.eye(2) / 2))
check_true("the broadcastable family {rho_diag, |0><0|, |1><1|} commutes pairwise; {|0><0|, |+><+|} does not",
           np.allclose(rho_diag @ np.diag([1, 0]) - np.diag([1, 0]) @ rho_diag, 0)
           and not np.allclose(np.diag([1, 0]) @ plus - plus @ np.diag([1, 0]), 0))

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[Q4] A classical (recorded) mediator cannot entangle; a coherent one can")
rng = np.random.default_rng(20261030)


def haar(n):
    z = (rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))) / math.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / abs(np.diag(r)))


def negativity_ab(rho_ab):
    pt = rho_ab.reshape(2, 2, 2, 2).transpose(0, 3, 2, 1).reshape(4, 4)
    ev = np.linalg.eigvalsh(pt)
    return float(-ev[ev < 0].sum())


def on(op2, pair):
    """Embed a two-qubit gate on qubits (A, M) = (0, 1) or (M, B) = (1, 2) of the order A, M, B."""
    return np.kron(op2, np.eye(2)) if pair == "AM" else np.kron(np.eye(2), op2)


def dephase_m(rho):
    """The record: the mediator is read in its basis by every witness, so its coherences vanish."""
    t = rho.reshape(2, 2, 2, 2, 2, 2).copy()
    for i in (0, 1):
        for j in (0, 1):
            if i != j:
                t[:, i, :, :, j, :] = 0
    return t.reshape(8, 8)


def run(coherent):
    plus_state = np.array([1, 1]) / math.sqrt(2)
    psi = np.kron(np.kron(plus_state, [1, 0]), plus_state)
    rho = np.outer(psi, psi.conj())
    for pair in ("AM", "MB", "AM"):
        u = on(haar(4), pair)
        rho = u @ rho @ u.conj().T
        if not coherent:
            rho = dephase_m(rho)
    t = rho.reshape(2, 2, 2, 2, 2, 2)
    return negativity_ab(np.einsum("ambcmd->abcd", t).reshape(4, 4))


neg_rec = [run(False) for _ in range(300)]
neg_coh = [run(True) for _ in range(300)]
check_true("recorded mediator: largest negativity over 300 random couplings is 0 (to 1e-12)", max(neg_rec) < 1e-12)
check_true(f"coherent mediator: the same couplings entangle in most trials (median negativity {np.median(neg_coh):.3f} > 0.01)",
           np.median(neg_coh) > 0.01)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[Q5] Gravitationally mediated entanglement, geometry of Bose et al. (2017)")
# Two masses mm, each in a superposition of two positions dx apart, centres dd apart, on one line. Branch distances dd (LL, RR),
# dd - dx (inner pair), dd + dx (outer pair). A coherent Newtonian field gives each branch the phase G mm^2 t / (hbar r).
mm, dd, dx = 1e-14, 450e-6, 250e-6
dist = {(0, 0): dd, (1, 1): dd, (1, 0): dd - dx, (0, 1): dd + dx}
rate = {key: G * mm * mm / (hbar * v) for key, v in dist.items()}
dphi_rate = rate[(1, 0)] + rate[(0, 1)] - rate[(0, 0)] - rate[(1, 1)]


def bmv_state(t):
    psi = np.array([np.exp(1j * rate[(i, j)] * t) for i in (0, 1) for j in (0, 1)]) / 2
    return np.outer(psi, psi.conj())


t_one, t_pi = 1.0 / dphi_rate, math.pi / dphi_rate
check("phase rate of the inner branch, G m^2 / (hbar (d - dx)), rad/s", rate[(1, 0)], 0.3164, rtol=2e-3)
check("entangling phase rate, rad/s", dphi_rate, 0.1256, rtol=2e-3)
check("time to an entangling phase of 1 rad, s", t_one, 7.96, rtol=2e-3)
check("time to an entangling phase of pi, s", t_pi, 25.0, rtol=2e-3)
check("negativity with a coherent field after 1 rad: sin(1/2)/2", negativity_ab(bmv_state(t_one)), math.sin(0.5) / 2, rtol=1e-9)
check("negativity with a coherent field at phase pi (maximal)", negativity_ab(bmv_state(t_pi)), 0.5, rtol=1e-9)
check("negativity with a recorded (classical) field at the same time", negativity_ab(np.diag(np.diag(bmv_state(t_pi)))), 0, atol=1e-12)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[Q6] Universality of free fall: an alpha-setting scalar, and a gravity that weighed only the Higgs share")


def f_coulomb(Z, A):
    """Electrostatic share of a nucleus' mass: Bethe-Weizsaecker Coulomb term a_C Z(Z-1)/A^(1/3), a_C = 0.711 MeV."""
    return 0.711 * Z * (Z - 1) / A ** (1 / 3) / (A * 931.494)


f_Ti, f_Pt = f_coulomb(22, 48), f_coulomb(78, 195)
earth = {(26, 56): 0.32, (8, 16): 0.30, (14, 28): 0.15, (12, 24): 0.14, (20, 40): 0.02, (13, 27): 0.02, (28, 58): 0.05}
f_E = sum(w * f_coulomb(Z, A) for (Z, A), w in earth.items()) / sum(earth.values())
check("electrostatic share of the mass, titanium-48", f_Ti, 2.02e-3, rtol=2e-2)
check("electrostatic share of the mass, platinum-195", f_Pt, 4.05e-3, rtol=2e-2)
eta_microscope = 2.7e-15   # MICROSCOPE 2022: (-1.5 +- 2.3 stat +- 1.5 syst) e-15
lam_max = math.sqrt(eta_microscope / (2 * f_E * (f_Pt - f_Ti)))
check("largest |d ln alpha / d phi| MICROSCOPE allows (phi in reduced Planck units)", lam_max, 2.1e-5, rtol=0.1)
u_MeV, me_MeV, mp_MeV, mn_MeV = 931.49410242, 0.51099895, 938.27208816, 939.56542052
atoms = {"Ti-48": (22, 48, 47.9479409), "Pt-195": (78, 195, 194.9647917)}
share = {key: (Z * me_MeV + 0.09 * (Z * mp_MeV + (A - Z) * mn_MeV)) / (M * u_MeV) for key, (Z, A, M) in atoms.items()}
eta_higgs = 2 * abs(share["Ti-48"] - share["Pt-195"]) / (share["Ti-48"] + share["Pt-195"])
check("predicted eta(Ti, Pt) if gravity weighed only the Higgs-given mass (nucleon share 9%)", eta_higgs, 1.0e-3, rtol=0.35)
check_true("that exceeds MICROSCOPE's bound by more than 1e11", eta_higgs > 1e11 * eta_microscope)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[Q7] Light bending: a scalar on the curvature term (Brans-Dicke) against Cassini")
w = sp.symbols("omega", positive=True)
gamma_bd = (1 + w) / (2 + w)
check_true("Brans-Dicke gamma - 1 = -1/(omega + 2)", sp.simplify(gamma_bd - 1 + 1 / (w + 2)) == 0)
check("smallest omega Cassini allows at 2 sigma (gamma - 1 >= -2.5e-5)", 1 / 2.5e-5 - 2, 39998.0)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[Q8] A massless spin-2 field in D spacetime dimensions")
D = sp.symbols("D", integer=True, positive=True)
pol = D * (D - 3) / 2
weyl = D**2 * (D**2 - 1) / 12 - D * (D + 1) / 2
check("polarisations in 3+1", pol.subs(D, 4), 2)
check("polarisations in 2+1", pol.subs(D, 3), 0, atol=1e-12)
check("Weyl components in 3+1", weyl.subs(D, 4), 10)
check("Weyl components in 2+1", weyl.subs(D, 3), 0, atol=1e-12)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[Q9] Single gravitons: where one quantum would hide behind its own horizon")
lam_min = math.sqrt(2 * h * G / c**3)        # 2 G (h c / lam) / c^4 = lam
E_th = h * c / lam_min
check("smallest wavelength outside its own horizon, in Planck lengths: sqrt(4 pi)", lam_min / L_P, math.sqrt(4 * math.pi))
check("threshold energy in Planck energies: sqrt(pi)", E_th / E_P, math.sqrt(math.pi))
check("a 100 Hz graviton over the threshold energy", h * 100.0 / E_th, 1.91e-41, rtol=1e-2)
check_true("GW150914 (about 3 solar masses at about 150 Hz) carried more than 1e78 quanta", 3.0 * M_sun * c**2 / (h * 150.0) > 1e78)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[Q10] Kerr black holes, units G = c = M = 1")


def r_plus(a_):
    return 1 + math.sqrt(1 - a_ * a_)


def m_irr(a_):
    return math.sqrt(r_plus(a_) / 2)          # M_irr^2 = A / 16 pi = (r+^2 + a^2) / 4 = r+ / 2 at M = 1


def r_isco(a_):
    z1 = 1 + (1 - a_ * a_) ** (1 / 3) * ((1 + a_) ** (1 / 3) + (1 - a_) ** (1 / 3))
    z2 = math.sqrt(3 * a_ * a_ + z1 * z1)
    return 3 + z2 - math.sqrt((3 - z1) * (3 + z1 + 2 * z2))


def eff(a_):
    r = r_isco(a_)
    return 1 - (r**1.5 - 2 * r**0.5 + a_) / (r**0.75 * math.sqrt(r**1.5 - 3 * r**0.5 + 2 * a_))


for a_ in (0.0, 0.5, 0.9, 0.998):
    check_true(f"spin {a_}: ergosphere at the equator (r = 2) lies outside the horizon r+ = {r_plus(a_):.3f}", 2 >= r_plus(a_))
spins = np.linspace(0, 0.999999, 50)
check_true("Christodoulou: M^2 = M_irr^2 + J^2 / (4 M_irr^2) holds for every spin (J = a at M = 1)",
           all(abs(m_irr(s) ** 2 + s * s / (4 * m_irr(s) ** 2) - 1) < 1e-9 for s in spins))
check("extractable share 1 - M_irr/M at maximal spin: 1 - 1/sqrt 2", 1 - m_irr(1.0), 1 - 1 / math.sqrt(2))
check("accretion efficiency without spin, 1 - sqrt(8/9)", eff(0.0), 1 - math.sqrt(8 / 9))
check("accretion efficiency at Thorne's limit a = 0.998", eff(0.998), 0.3208, rtol=2e-3)
check("accretion efficiency as the spin approaches 1 (a = 1 - 1e-10), tending to 1 - 1/sqrt 3", eff(1 - 1e-10), 1 - 1 / math.sqrt(3), rtol=2e-3)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[Q11] Hawking radiation of real black holes")
T_cmb = 2.7255
check_true(f"a solar-mass hole ({T_H_sun:.2e} K) is colder than the microwave sky ({T_cmb} K): it absorbs more than it emits",
           T_H_sun < T_cmb)
M_eq = hbar * c**3 / (8 * math.pi * G * kB * T_cmb)
check("mass whose Hawking temperature equals the sky's, in units of the Moon's mass (7.342e22 kg)", M_eq / 7.342e22, 0.61, rtol=0.02)
t_ev = 5120 * math.pi * G**2 * M_sun**3 / (hbar * c**4) / year
check_true(f"evaporation time of a solar-mass hole in empty space, Stefan-Boltzmann estimate 5120 pi G^2 M^3/(hbar c^4): {t_ev:.1e} yr > 1e66 yr",
           t_ev > 1e66)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[Q12] The universe at its own Schwarzschild threshold")
H_, G_, c_ = sp.symbols("H G c", positive=True)
rho = 3 * H_**2 / (8 * sp.pi * G_)
M_H = sp.Rational(4, 3) * sp.pi * rho * (c_ / H_) ** 3
check_true("2 G M_H / c^2 = c / H exactly, at every epoch", sp.simplify(2 * G_ * M_H / c_**2 - c_ / H_) == 0)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[Q13] Inflation and the late universe (Planck 2018: Omega_m = 0.315, Omega_L = 0.685, |Omega_k| < 0.005)")
Om, OL, Ok_bound = 0.315, 0.685, 0.005
T_reh, T_eq, z_eq = 1e15 * 1e9, 0.80, 3400.0      # eV
growth = (T_reh / T_eq) ** 2 * (1 + z_eq)
N_min = 0.5 * math.log(growth / Ok_bound)
check("growth of |Omega - 1| from reheating at 1e15 GeV to today", growth, 5.3e51, rtol=0.05)
check("e-folds that bring |Omega - 1| = 1 down to Planck's bound", N_min, 62.0, rtol=0.02)
zs = np.linspace(5, -0.999, 2000)
H = np.sqrt(Om * (1 + zs) ** 3 + OL)
check_true("the Hubble rate falls at every step from z = 5 into the far future", all(np.diff(H) < 0))
check("its floor, the de Sitter rate, over today's: sqrt(Omega_L)", math.sqrt(OL), 0.8276, rtol=1e-3)
check("onset of the present acceleration, z = (2 Omega_L / Omega_m)^(1/3) - 1", (2 * OL / Om) ** (1 / 3) - 1, 0.6315, rtol=2e-3)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[Q14] Primordial tensor modes: a quantum signature of the metric")
H_s = sp.symbols("H_s", positive=True)
hbar_s, G_s, c_s = sp.symbols("hbar G c", positive=True)
Mpl2 = hbar_s * c_s / (8 * sp.pi * G_s)                          # reduced Planck mass squared (kg^2)
P_t = 2 / sp.pi**2 * (hbar_s * H_s) ** 2 / (Mpl2 * c_s**4)       # (2/pi^2)(hbar H / M_pl c^2)^2
check_true("P_t = (2/pi^2)(hbar H / M_pl c^2)^2 = 16 G hbar H^2 / (pi c^5): linear in hbar, zero for a classical metric",
           sp.simplify(P_t - 16 * G_s * hbar_s * H_s**2 / (sp.pi * c_s**5)) == 0 and sp.limit(P_t, hbar_s, 0) == 0)
A_s, r_max = 2.1e-9, 0.036                                       # Planck 2018 scalar amplitude; BICEP/Keck 2021, 95%
M_pl_GeV = math.sqrt(hbar * c / (8 * math.pi * G)) * c**2 / GeV
V14 = (1.5 * math.pi**2 * A_s * r_max) ** 0.25 * M_pl_GeV
check("energy scale of inflation at the bound r = 0.036, V^(1/4) in GeV", V14, 1.4e16, rtol=0.03)
H_inf = math.pi * M_pl_GeV * math.sqrt(A_s * r_max / 2)
check_true(f"Hubble rate during inflation at that bound, hbar H = {H_inf:.1e} GeV, below 1e14 GeV", H_inf < 1e14)
N60 = 60
r_staro = 12 / N60**2
check("Starobinsky inflation, r = 12 / N^2 at N = 60", r_staro, 3.33e-3, rtol=1e-2)
check("single-field consistency relation, n_t = -r/8, for that r", -r_staro / 8, -4.17e-4, rtol=1e-2)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[Q15] Can dark matter be neutrinos?")
h_little, omega_c, omega_b = 0.674, 0.120, 0.0224               # Planck 2018
for msum in (0.06, 0.072):
    omega_nu = msum / 93.14
    print(f"     sum of masses {msum} eV: Omega_nu h^2 = {omega_nu:.2e}, share of the dark matter density {omega_nu / omega_c:.3%}")
check_true("at the cosmological bound (0.072 eV, DESI 2024) neutrinos are less than 1% of the dark matter density",
           0.072 / 93.14 / omega_c < 0.01)
# Pauli bound: a fermion of mass m with g states has phase-space density at most g / (2 pi hbar)^3, so a halo of density rho whose
# particles move slower than v_max needs rho <= m g (4 pi / 3)(m v_max)^3 / (2 pi hbar)^3. A dwarf spheroidal galaxy: central
# density 0.1 solar masses per cubic parsec, velocity dispersion 10 km/s; generously v_max = 3 sigma; g = 2 per flavour.
rho_dw, v_max, g_nu = 0.1 * M_sun / pc**3, 3 * 10e3, 2
m4 = rho_dw * (2 * math.pi * hbar) ** 3 / (g_nu * 4 * math.pi / 3 * v_max**3)
m_min_eV = m4 ** 0.25 * c**2 / eV
check_true(f"a dwarf galaxy made of neutrinos needs m > {m_min_eV:.0f} eV, more than 1000 times the cosmological bound", m_min_eV > 1000 * 0.072)
T_nu = 1.945 * kB / eV                                          # relic neutrino temperature today, eV
v_relic = 3.15 * T_nu / 0.05 * c                                # mean momentum 3.15 T over m = 0.05 eV
v_esc = 533e3                                                   # local Galactic escape speed, m/s (Piffl et al. 2014)
check_true(f"relic neutrinos of 0.05 eV move at {v_relic / 1e3:.0f} km/s, faster than the Galactic escape speed of 533 km/s",
           v_relic > v_esc)
v_star = c * (1 - 0.5 * (0.05 / 1e6) ** 2)                     # a 1 MeV neutrino from a star
check_true("a 1 MeV stellar neutrino moves within 1e-14 of c, more than 500 times the escape speed", v_star > 500 * v_esc)
check("baryon share of the matter, Omega_b / Omega_m, as measured at recombination", omega_b / (omega_b + omega_c), 0.157, rtol=5e-3)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[Q16] alpha as the strength with which charge interacts with itself")
a_e_measured = 1.15965218059e-3                                 # Fan et al. 2023
check_true(f"Schwinger's first-order term alpha/2pi = {alpha / (2 * math.pi):.8f} is within 0.2% of the measured a_e",
           abs(alpha / (2 * math.pi) / a_e_measured - 1) < 2e-3)
r_e = e_charge**2 / (4 * math.pi * eps0 * m_e * c**2)
lamC_bar = hbar / (m_e * c)
a0 = 4 * math.pi * eps0 * hbar**2 / (m_e * e_charge**2)
check("classical electron radius over reduced Compton wavelength = alpha", r_e / lamC_bar, alpha, rtol=1e-8)
check("reduced Compton wavelength over Bohr radius = alpha", lamC_bar / a0, alpha, rtol=1e-8)
ratio = G * m_p * m_e / (e_charge**2 / (4 * math.pi * eps0))
check("gravity over electric attraction in hydrogen, at every distance", ratio, 4.41e-40, rtol=1e-2)
check("gravitational coupling of the electron, G m_e^2 / (hbar c)", G * m_e**2 / (hbar * c), 1.75e-45, rtol=1e-2)
inv_alpha_mz, s2w, m_Z = 127.951, 0.23122, 91.1876                 # PDG 2024, MS-bar at the Z mass; GeV
inv_a1, inv_a2 = 0.6 * (1 - s2w) * inv_alpha_mz, s2w * inv_alpha_mz  # hypercharge (GUT-normalised) and SU(2)
b1, b2 = 41 / 10, -19 / 6                                           # Standard Model one-loop coefficients
t_run = math.log(E_P / GeV / m_Z)
inv_alpha_P = 5 / 3 * (inv_a1 - b1 / (2 * math.pi) * t_run) + (inv_a2 - b2 / (2 * math.pi) * t_run)
check("1/alpha at the Planck energy, Standard Model at one loop", inv_alpha_P, 105.0, rtol=0.02)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[Q17] The speed of gravity")
D_L = 40 * Mpc
dt = 1.74
check_true(f"GW170817: 1.74 s over 40 Mpc gives |v_gw/c - 1| about {dt * c / D_L:.1e}, below 1e-15", dt * c / D_L < 1e-15)

print(f"\n{sum(results)} of {len(results)} checks passed")
raise SystemExit(0 if all(results) else 1)
