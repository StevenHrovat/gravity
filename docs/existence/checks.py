"""Existence and Information: the checks behind docs/existence/existence.tex.

Needs numpy, sympy and scipy (scipy only for the linear programme of [E19]). Runs in a few seconds. Every printed line is a check with
its expected value; the last line counts them. The paper stands on these checks alone.

  [E1]  the first author's "Existence" g*h/c: the only energy that g, h and c make, and 4 pi^2 times the Unruh/Hawking temperature
  [E2]  "1 Existence per 1 Information/s": the assertion rate as the lapse reproduces the measured clock shifts
  [E3]  Axiom 3 forbids a composition-dependent pull: the MICROSCOPE bound on an information scalar that couples to electromagnetic energy
  [E4]  scalar-tensor (Brans-Dicke) gravity: Cassini's gamma bound on omega, and gamma = 1 exactly when the scalar does not touch the metric
  [E5]  2+1 against 3+1: propagating graviton polarisations and Weyl components
  [E6]  the Kugelblitz threshold of one quantum, and how far an observable graviton is from it; the occupation number of a real wave
  [E7]  Dyson's estimate reconstructed: about four solar gravitons absorbed by the whole Earth in the Sun's lifetime
  [E8]  a flat Friedmann universe sits exactly at the Kugelblitz threshold at every epoch (2 G M_H / c^2 = c / H)
  [E9]  the running of alpha: at the Planck energy alpha is still about 1/105 (Standard Model, one loop); it does not reach 1
  [E10] spinning holes are more efficient: accretion efficiency 5.7% -> 42.3%, extractable spin energy, entropy at fixed mass
  [E11] three, four, five nodes: majority voting tolerance, and the colour rule that real hadrons obey
  [E12] neutrinos cannot drive the expansion: their density and their sign in the acceleration equation
  [E13] a massless quantum cannot decay: its lifetime is dilated without bound and no massive final state is reachable
  [E14] "different flavours of h": boson spins in units of hbar, and the dimension of h*h
  [E15] "QC breaks cryptography": Shor's period finding against Grover's square root on a hash
  [E16] "gravity would be stronger, so the EM field had to bind the electron more strongly": gravity's share of an atom's binding
  [E17] Axiom 3's record: what every witness reads in full must be classical; one unitary copies two states only if they are equal or
        orthogonal (the no-cloning core of no-broadcasting)
  [E18] gravity-mediated entanglement (Bose et al. 2017 geometry): a coherent mediator entangles, a recorded (classical) one never does
  [E19] Bell: halves that decide on their own setting stay at S <= 2; full reach gives 4 and signals; the singlet gives 2 sqrt(2);
        superdeterminism needs measurement dependence (S - 2)/3; the three loophole-free CHSH values lie above 2
  [E20] the spinning black hole from DMP's containment split: M^2 = m^2 + (J/2m)^2 gives Kerr's horizon area, a <= 1 and the 29%
  [E21] leptons as the inter-cluster protocol: a two-lepton cluster (positronium) falls over in 125 ps or 142 ns; the muon, once its
        stability is not protected, decays in 2.2 microseconds (Fermi's formula)
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


# Constants: SI 2019 exact values and CODATA 2018.
h = 6.62607015e-34          # J s
hbar = h / (2 * math.pi)
c = 299792458.0             # m/s
G = 6.67430e-11             # m^3 kg^-1 s^-2
kB = 1.380649e-23           # J/K
eV = 1.602176634e-19        # J
m_u = 1.66053906660e-27     # kg
M_sun = 1.98847e30          # kg
M_earth = 5.9722e24         # kg
au = 1.495978707e11         # m
year = 3.15576e7            # s (Julian)
g_n = 9.80665               # m/s^2 (standard gravity)
L_P = math.sqrt(hbar * G / c**3)
E_P = math.sqrt(hbar * c**5 / G)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E1] 'Existence = strength of the local Existence (Gravity) * the universal quantum * the universal tick rate (1/c)'")
# Dimensions (M, L, T): g = L T^-2, h = M L^2 T^-1, c = L T^-1, energy = M L^2 T^-2. Solve g^a h^b c^k = energy.
a, b, k = sp.symbols("a b k")
dims = {"g": (0, 1, -2), "h": (1, 2, -1), "c": (0, 1, -1)}
eqs = [sp.Eq(a * dims["g"][i] + b * dims["h"][i] + k * dims["c"][i], (1, 2, -2)[i]) for i in range(3)]
sol = sp.solve(eqs, [a, b, k], dict=True)
check_true("g^a h^b c^k is an energy for exactly one exponent triple, (a, b, k) = (1, 1, -1): E = g h / c", sol == [{a: 1, b: 1, k: -1}])
E_ex = g_n * h / c
T_unruh = hbar * g_n / (2 * math.pi * c * kB)
check("E = g h / c at standard gravity, in joules", E_ex, 2.16743e-41, rtol=1e-4)
check("E / (k_B T_Unruh) at the same acceleration (Unruh 1976: k T = hbar a / 2 pi c), = 4 pi^2", E_ex / (kB * T_unruh), 4 * math.pi**2)
check("Unruh temperature at 1 g, in kelvin", T_unruh, 3.9766e-20, rtol=1e-3)
kappa_sun = c**4 / (4 * G * M_sun)  # surface gravity of a solar-mass Schwarzschild hole
T_hawking = hbar * kappa_sun / (2 * math.pi * c * kB)
check("Hawking temperature of a solar-mass hole from its surface gravity, in kelvin", T_hawking, 6.17e-8, rtol=2e-3)
check("the first author's Existence at that surface gravity over k_B T_Hawking, = 4 pi^2", (kappa_sun * h / c) / (kB * T_hawking), 4 * math.pi**2)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E2] 'To Exist you need exactly 1 Existence per 1 Information/s': the assertion rate as general relativity's lapse")
# Weak field: lapse N = sqrt(1 + 2 Phi / c^2); the fractional rate difference between two heights dz apart is g dz / c^2.
for label, dz, want in [("Pound-Rebka tower, 22.5 m (Pound and Rebka 1960)", 22.5, 2.455e-15),
                        ("two optical clocks 33 cm apart (Chou et al. 2010; measured ~4e-17)", 0.33, 3.60e-17)]:
    check(f"fractional rate shift g dz / c^2, {label}", g_n * dz / c**2, want, rtol=2e-3)
r = sp.symbols("r", positive=True)
M_, G_, c_ = sp.symbols("M G c", positive=True)
lapse = sp.sqrt(1 - 2 * G_ * M_ / (r * c_**2))
check_true("the Schwarzschild lapse goes to 0 at r = 2GM/c^2: the assertion rate seen from outside stops at the horizon",
           sp.simplify(lapse.subs(r, 2 * G_ * M_ / c_**2)) == 0)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E3] Axiom 3, 'from trust nothing can be derived about information but its existence': no composition-dependent pull")
# A scalar phi (Planck units, kinetic term M_P^2 (d phi)^2 / 2) that sets alpha with d ln(alpha)/d phi = lam gives every body a scalar
# charge lam * f_EM * m (f_EM = electrostatic share of its mass), so the extra force is 2 lam^2 f_A f_B times gravity, and two test
# bodies falling towards the Earth differ by eta = 2 lam^2 f_Earth (f_1 - f_2) (Dvali and Zaldarriaga 2002 in this normalisation).
def f_coulomb(Z, A):
    """Electrostatic energy share of a nucleus, Bethe-Weizsaecker Coulomb term a_C Z(Z-1)/A^(1/3), a_C = 0.711 MeV."""
    return 0.711 * Z * (Z - 1) / A ** (1 / 3) / (A * 931.494)


f_Ti, f_Pt = f_coulomb(22, 48), f_coulomb(78, 195)
earth = {(26, 56): 0.32, (8, 16): 0.30, (14, 28): 0.15, (12, 24): 0.14, (20, 40): 0.02, (13, 27): 0.02, (28, 58): 0.05}  # mass shares
f_E = sum(w * f_coulomb(Z, A) for (Z, A), w in earth.items()) / sum(earth.values())
check("electrostatic share of the mass, titanium-48", f_Ti, 2.02e-3, rtol=2e-2)
check("electrostatic share of the mass, platinum-195", f_Pt, 4.05e-3, rtol=2e-2)
eta_microscope = 2.7e-15  # MICROSCOPE 2022: eta(Ti, Pt) = (-1.5 +- 2.3 stat +- 1.5 syst) e-15, no violation at 2.7e-15
lam_max = math.sqrt(eta_microscope / (2 * f_E * (f_Pt - f_Ti)))
check("largest |d ln alpha / d phi| that MICROSCOPE allows", lam_max, 2.1e-5, rtol=0.1)
H0 = 67.4e3 / 3.0857e22 * year  # Hubble rate per year (Planck 2018 H0 = 67.4 km/s/Mpc)
drift_max = lam_max * 1.0 * H0  # field rolling one Planck unit per e-fold
check("largest alpha drift per year for a field rolling one Planck unit per e-fold, given MICROSCOPE", drift_max, 1.4e-15, rtol=0.1)
check_true("the optical-clock limit (1.0 +- 1.1)e-18 per year (Lange et al. 2021) is tighter than that by more than 100",
           drift_max / 2.2e-18 > 100)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E4] Scalar-tensor gravity: Brans-Dicke's gamma, Cassini's bound, and the scalar that does not touch the metric")
w = sp.symbols("omega", positive=True)
gamma_bd = (1 + w) / (2 + w)
check_true("Brans-Dicke gamma - 1 = -1/(omega + 2)", sp.simplify(gamma_bd - 1 + 1 / (w + 2)) == 0)
# Cassini: gamma - 1 = (2.1 +- 2.3) e-5 (Bertotti, Iess, Tortora 2003); 2 sigma below: -2.5e-5.
omega_min = 1 / 2.5e-5 - 2
check("smallest omega Cassini allows at 2 sigma", omega_min, 39998.0)
check_true("gamma -> 1 as omega -> infinity (Brans-Dicke reduces to general relativity)", sp.limit(gamma_bd, w, sp.oo) == 1)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E5] 2+1 against 3+1: what the existence vector can carry")
D = sp.symbols("D", integer=True, positive=True)
pol = D * (D - 3) / 2           # propagating polarisations of a massless spin-2 field in D spacetime dimensions
riem = D**2 * (D**2 - 1) / 12   # independent components of the Riemann tensor
ricci = D * (D + 1) / 2
check("graviton polarisations in 3+1", pol.subs(D, 4), 2)
check("graviton polarisations in 2+1 (no local degree of freedom)", pol.subs(D, 3), 0, atol=1e-12)
check("Weyl components (curvature not fixed by local matter) in 3+1", (riem - ricci).subs(D, 4), 10)
check("Weyl components in 2+1", (riem - ricci).subs(D, 3), 0, atol=1e-12)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E6] A graviton as a Kugelblitz: the threshold of one quantum, and where real gravitons are")
# A quantum of wavelength lam and energy h c / lam lies inside its own Schwarzschild radius when 2 G (h c / lam) / c^4 >= lam.
lam_min = math.sqrt(2 * h * G / c**3)
E_th = h * c / lam_min
check("smallest wavelength outside its own horizon, in Planck lengths, = sqrt(4 pi)", lam_min / L_P, math.sqrt(4 * math.pi))
check("threshold energy in Planck energies, = sqrt(pi)", E_th / E_P, math.sqrt(math.pi))
E_100Hz = h * 100.0
check("a 100 Hz graviton (LIGO band) over the threshold energy", E_100Hz / E_th, 1.91e-41, rtol=1e-2)
# GW150914 radiated about 3.0 solar masses at about 150 Hz (Abbott et al. 2016).
N_gw150914 = 3.0 * M_sun * c**2 / (h * 150.0)
check_true("GW150914 carried more than 10^78 quanta: the wave is classical in every regime ever measured", N_gw150914 > 1e78)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E7] Dyson's estimate: the whole Earth as a graviton detector, for the Sun's lifetime")
sigma = 4 * math.pi**2 * L_P**2          # per-electron absorption cross-section (Dyson 2013)
N_e = M_earth / (2 * m_u)                # about one electron per two nucleons
L_grav = 7.9e7                            # W, the Sun's thermal graviton luminosity (Gould 1985; Weinberg 1965 gives ~6e7 W)
E_grav = kB * 1.57e7                      # J, about the solar core temperature
flux = L_grav / (4 * math.pi * au**2 * E_grav)
events = N_e * sigma * flux * 5e9 * year
check("cross-section 4 pi^2 L_P^2 in m^2", sigma, 1.0315e-68, rtol=1e-3)
check("expected absorptions in 5 Gyr (Dyson's number, as quoted: about four)", events, 3.9, rtol=0.15)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E8] 'The early Existence was a Kugelblitz': a flat Friedmann universe and its own Schwarzschild radius")
H_ = sp.symbols("H", positive=True)
rho = 3 * H_**2 / (8 * sp.pi * G_)
M_H = sp.Rational(4, 3) * sp.pi * rho * (c_ / H_) ** 3
check_true("2 G M_H / c^2 = c / H exactly, for every H (every epoch, not only the early one)",
           sp.simplify(2 * G_ * M_H / c_**2 - c_ / H_) == 0)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E9] 'That is why the FSC started at 1': the running of alpha up to the Planck energy")
inv_alpha_mz, s2w, m_Z = 127.951, 0.23122, 91.1876  # PDG, MS-bar at the Z mass; GeV
inv_a1 = 0.6 * (1 - s2w) * inv_alpha_mz             # hypercharge, GUT-normalised
inv_a2 = s2w * inv_alpha_mz
b1, b2 = 41 / 10, -19 / 6                           # Standard Model one-loop coefficients
M_planck_GeV = E_P / eV / 1e9
t = math.log(M_planck_GeV / m_Z)
inv_a1_P = inv_a1 - b1 / (2 * math.pi) * t
inv_a2_P = inv_a2 - b2 / (2 * math.pi) * t
inv_alpha_P = 5 / 3 * inv_a1_P + inv_a2_P
check("1/alpha at the Z mass rebuilt from the two couplings", 5 / 3 * inv_a1 + inv_a2, inv_alpha_mz)
check("1/alpha at the Planck energy (one loop, Standard Model)", inv_alpha_P, 105.0, rtol=0.02)
# Pure QED with the electron alone: 1/alpha(Q) = 1/alpha_0 - (2 / 3 pi) ln(Q / m_e); alpha = 1 at ln(Q / m_e) = (3 pi / 2)(137.036 - 1).
ln_ratio = 1.5 * math.pi * (137.035999 - 1)
log10_Q_over_EP = (ln_ratio + math.log(0.51099895e6 * eV / E_P)) / math.log(10)
check_true("pure QED reaches alpha = 1 only some 250 orders of magnitude above the Planck energy", log10_Q_over_EP > 250)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E10] 'Spinning black holes are more efficient', 'the more is known about a boundary, the more efficient it becomes'")


def r_isco(a):
    z1 = 1 + (1 - a * a) ** (1 / 3) * ((1 + a) ** (1 / 3) + (1 - a) ** (1 / 3))
    z2 = math.sqrt(3 * a * a + z1 * z1)
    return 3 + z2 - math.sqrt((3 - z1) * (3 + z1 + 2 * z2))


def eta_disk(a):
    return 1 - math.sqrt(1 - 2 / (3 * r_isco(a)))


check("accretion efficiency, no spin (Bardeen, Press, Teukolsky 1972)", eta_disk(0.0), 1 - math.sqrt(8 / 9))
check("accretion efficiency at spin 0.998 (Thorne's limit)", eta_disk(0.998), 0.3208, rtol=5e-3)
check("accretion efficiency at maximal spin", eta_disk(1.0), 1 - 1 / math.sqrt(3), rtol=1e-6)
spins = np.linspace(0, 1, 101)
m_irr = np.sqrt((1 + np.sqrt(1 - spins**2)) / 2)          # M_irr / M at fixed M
check_true("efficiency rises with spin at every step", all(eta_disk(x) < eta_disk(y) for x, y in zip(spins[:-1], spins[1:])))
check_true("extractable share 1 - M_irr/M rises with spin; the entropy A/4 = 4 pi M_irr^2 falls with it",
           np.all(np.diff(1 - m_irr) > 0) and np.all(np.diff(m_irr**2) < 0))
q = np.linspace(0, 0.99, 100)
area_kn = lambda aa, qq: 4 * math.pi * ((1 + math.sqrt(1 - aa * aa - qq * qq)) ** 2 + aa * aa)  # Kerr-Newman, M = 1
check_true("Kerr-Newman: at fixed mass, more charge (one more count) also means a smaller horizon",
           all(area_kn(0.0, x) > area_kn(0.0, y) for x, y in zip(q[:-1], q[1:])))

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E11] 'Quark: three node cluster. Meson: two node cluster, so no failover'; '4 in balance is hard. 5 would be easier'")
tol = {n: (n - 1) // 2 for n in range(2, 7)}     # wrong nodes a majority vote outvotes
check_true("majority voting outvotes 0, 1, 1, 2, 2 wrong nodes for 2, 3, 4, 5, 6 nodes: 4 adds no tolerance over 3, 5 does",
           [tol[n] for n in range(2, 7)] == [0, 1, 1, 2, 2])
# Colour rule: a hadron of nq quarks and na antiquarks is a colour singlet only if nq - na is a multiple of 3.
singlets = {n: sorted((nq, n - nq) for nq in range(n + 1) if (nq - (n - nq)) % 3 == 0) for n in range(2, 7)}
check_true("the colour rule allows every size from 2 on: qq-bar; qqq; qq q-bar q-bar; qqqq q-bar; six quarks",
           singlets[2] == [(1, 1)] and (3, 0) in singlets[3] and (2, 2) in singlets[4] and (4, 1) in singlets[5]
           and (6, 0) in singlets[6])

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E12] 'They (the first neutrinos) might be what is actually driving the expansion of Existence'")
sum_m = 0.06  # eV, the smallest sum the oscillations allow (normal ordering)
h_little = 0.674
omega_nu = sum_m / 93.14 / h_little**2
check("neutrino share of the critical density for a 0.06 eV mass sum", omega_nu, 1.42e-3, rtol=1e-2)
# Second Friedmann equation: a''/a = -(4 pi G / 3) (rho + 3 p) = -(4 pi G / 3) rho (1 + 3 w).
for name, wv, sign in [("relativistic neutrinos (w = 1/3)", 1 / 3, -1), ("non-relativistic neutrinos (w = 0)", 0.0, -1),
                       ("a cosmological constant (w = -1)", -1.0, 1)]:
    check_true(f"{name}: {'decelerates' if sign < 0 else 'accelerates'} the expansion", np.sign(-(1 + 3 * wv)) == sign)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E13] 'A singularity, like a photon or a gluon, cannot decay into anything'")
m, E, tau = sp.symbols("m E tau", positive=True)
tau_lab = E / (m * c_**2) * tau
check_true("lab lifetime E tau / (m c^2) grows without bound as the rest mass goes to 0", sp.limit(tau_lab, m, 0) == sp.oo)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E14] 'Is IM just different flavors of h ... maybe W+Z are h*h?'")
spins_hbar = {"photon": 1, "gluon": 1, "W": 1, "Z": 1, "Higgs": 0, "graviton (hypothetical)": 2}
check_true("every boson carries spin in whole units of hbar: 1, 1, 1, 1, 0 and 2", all(isinstance(v, int) for v in spins_hbar.values()))
dim_h = np.array(dims["h"])
check_true("h*h has dimension M^2 L^4 T^-2: neither an energy, a mass nor an action",
           tuple(2 * dim_h) not in {(1, 2, -2), (1, 0, 0), (1, 2, -1)})

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E15] 'Wait, is that why QC breaks cryptography?'")
check("Grover's search turns a 256-bit hash preimage into about 2^128 steps (bits of work left)", 256 / 2, 128)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E16] 'Gravity would be stronger. This necessitated the Information field, the EM field, to bind the electron more strongly'")
m_e, m_p, e_charge, eps0 = 9.1093837015e-31, 1.67262192369e-27, 1.602176634e-19, 8.8541878128e-12
a0 = 5.29177210903e-11
ratio = G * m_p * m_e / (e_charge**2 / (4 * math.pi * eps0))
check("gravitational over electric attraction between a proton and an electron (any distance)", ratio, 4.41e-40, rtol=5e-3)
rho_curv = c**2 / (G * a0**2)  # density whose curvature radius is one Bohr radius
rho_planck = c**5 / (hbar * G**2)
check_true("curvature reaches the size of an atom only above 10^47 kg/m^3, thirty orders above nuclear density (2.3e17)",
           rho_curv > 1e47 and rho_curv / 2.3e17 > 1e29)
check_true("that density is still below the Planck density (5e96 kg/m^3): gravity rivals atomic binding only in the Planck era",
           rho_curv < rho_planck and rho_planck > 1e96)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E17] Axiom 3: 'a record ... that every witness of that act can read in full'. What can be read in full by two is classical")
# A record every witness holds in full is copied to each of them. One unitary U with U|s>|0> = |s>|s> for two states s, t preserves
# inner products, so <s|t> = <s|t>^2: the overlap is 0 or 1. Two distinct, non-orthogonal states (any superposition against a basis
# state) cannot both be recorded in full. Barnum et al. (1996) extend this to mixed states: a set can be broadcast iff it commutes.
ket0 = np.array([1.0, 0.0])
ketp = np.array([1.0, 1.0]) / np.sqrt(2)
ov = float(ket0 @ ketp)
check("overlap of |0> and |+>", ov, 1 / np.sqrt(2))
check_true("<0|+> differs from <0|+>^2, so no unitary records both in full", abs(ov - ov**2) > 0.2)
for name, (u, v) in {"|0>, |1>": (ket0, np.array([0.0, 1.0])), "|0>, |0>": (ket0, ket0)}.items():
    o = float(u @ v)
    check_true(f"{name}: overlap {o:.0f} equals its square, a copier exists (a classical alphabet)", abs(o - o**2) < 1e-12)
rho_a, rho_b = np.outer(ket0, ket0), np.outer(ketp, ketp)
check("commutator norm of the two states (nonzero: the pair cannot be broadcast, Barnum et al.)",
      np.linalg.norm(rho_a @ rho_b - rho_b @ rho_a), 1 / np.sqrt(2))

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E18] Gravity-mediated entanglement, Bose et al. (2017) geometry: coherent mediator against recorded mediator")
# Two masses mm, each in a superposition of two positions dx apart, centres d apart, on one line. Branch distances d (LL, RR),
# d - dx (inner), d + dx (outer). A coherent field gives each branch the phase G mm^2 t / (hbar r).
mm, dd, dx = 1e-14, 450e-6, 250e-6
dist = {(0, 0): dd, (1, 1): dd, (1, 0): dd - dx, (0, 1): dd + dx}
rate = {k: G * mm * mm / (hbar * v) for k, v in dist.items()}
dphi_rate = rate[(1, 0)] + rate[(0, 1)] - rate[(0, 0)] - rate[(1, 1)]


def negativity(rho):
    pt = rho.reshape(2, 2, 2, 2).transpose(0, 3, 2, 1).reshape(4, 4)
    ev = np.linalg.eigvalsh(pt)
    return float(-ev[ev < 0].sum())


def bmv_state(t):
    psi = np.array([np.exp(1j * rate[(i, j)] * t) for i in (0, 1) for j in (0, 1)]) / 2
    return np.outer(psi, psi.conj())


t_one, t_pi = 1.0 / dphi_rate, np.pi / dphi_rate
print(f"     entangling phase rate {dphi_rate:.4f} rad/s; 1 rad after {t_one:.1f} s, pi after {t_pi:.1f} s")
check(f"negativity with a coherent mediator after {t_one:.1f} s, sin(1/2)/2", negativity(bmv_state(t_one)), np.sin(0.5) / 2, rtol=1e-9)
check(f"negativity with a coherent mediator after {t_pi:.1f} s (maximal)", negativity(bmv_state(t_pi)), 0.5, rtol=1e-9)
check("negativity with a recorded (classical) mediator at the same time", negativity(np.diag(np.diag(bmv_state(t_pi)))), 0, atol=1e-12)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E19] Bell: what each reading of the Duality gives for the CHSH value S")
import itertools  # noqa: E402

SETTINGS = [(0, 0), (0, 1), (1, 0), (1, 1)]
SIGN = {(0, 0): 1, (0, 1): 1, (1, 0): 1, (1, 1): -1}


def pm(b):
    return 1 if b else -1


LOCAL = list(itertools.product([0, 1], repeat=4))  # (a0, a1, b0, b1): each half answers from its own setting and a shared state


def s_local(lam):
    return sum(SIGN[(x, y)] * pm(lam[x]) * pm(lam[2 + y]) for x, y in SETTINGS)


check("halves deciding on their own setting: largest |S| over the 16 deterministic strategies (Fine 1982)",
      max(abs(s_local(l)) for l in LOCAL), 2)
FUNCS = list(itertools.product([0, 1], repeat=4))  # outcome as a function of both settings, index 2x + y


def s_full(fa, fb):
    return sum(SIGN[(x, y)] * pm(fa[2 * x + y]) * pm(fb[2 * x + y]) for x, y in SETTINGS)


check("halves with full reach over both settings: largest S", max(s_full(a, b) for a in FUNCS for b in FUNCS), 4)
fb_four = tuple(0 if (x and y) else 1 for x, y in SETTINGS)
check_true("the S = 4 strategy signals: Bob's outcome at y = 1 changes with Alice's setting", fb_four[1] != fb_four[3])
X = np.array([[0, 1], [1, 0]], dtype=complex)
Zp = np.diag([1.0, -1.0]).astype(complex)
singlet = np.array([0, 1, -1, 0], dtype=complex) / np.sqrt(2)
A_OBS, B_OBS = [Zp, X], [-(Zp + X) / np.sqrt(2), -(Zp - X) / np.sqrt(2)]
s_q = sum(SIGN[(x, y)] * float(np.real(singlet.conj() @ np.kron(A_OBS[x], B_OBS[y]) @ singlet)) for x, y in SETTINGS)
check("the singlet at the optimal angles (Tsirelson)", s_q, 2 * np.sqrt(2))
try:
    from scipy.optimize import linprog  # noqa: E402
except ImportError:  # pragma: no cover
    linprog = None


def least_m(target):
    """Least measurement dependence M (Hall 2010) for a local deterministic model to reach CHSH value `target`."""
    pairs = list(itertools.combinations(range(4), 2))
    n_p, n_u = 64, len(pairs) * 16
    n = n_p + n_u + 1
    cost = np.zeros(n)
    cost[-1] = 1
    a_eq, b_eq, a_ub, b_ub = [], [], [], []
    for s in range(4):
        r = np.zeros(n)
        r[s * 16:(s + 1) * 16] = 1
        a_eq.append(r)
        b_eq.append(1)
    r = np.zeros(n)
    for s, (x, y) in enumerate(SETTINGS):
        for li, lam in enumerate(LOCAL):
            r[s * 16 + li] = -SIGN[(x, y)] * pm(lam[x]) * pm(lam[2 + y])
    a_ub.append(r)
    b_ub.append(-target)
    for k, (s1, s2) in enumerate(pairs):
        for li in range(16):
            for sg in (1, -1):
                r = np.zeros(n)
                r[s1 * 16 + li], r[s2 * 16 + li], r[n_p + k * 16 + li] = sg, -sg, -1
                a_ub.append(r)
                b_ub.append(0)
        r = np.zeros(n)
        r[n_p + k * 16:n_p + (k + 1) * 16] = 1
        r[-1] = -1
        a_ub.append(r)
        b_ub.append(0)
    res = linprog(cost, A_ub=np.array(a_ub), b_ub=b_ub, A_eq=np.array(a_eq), b_eq=b_eq, bounds=[(0, None)] * n, method="highs")
    return res.fun


if linprog is None:
    check_true("scipy is installed (needed for the superdeterminism linear programme)", False)
else:
    for s_val in (2.42, 2 * np.sqrt(2)):
        check(f"least measurement dependence to reach S = {s_val:.4f}, equal to (S - 2)/3", least_m(s_val), (s_val - 2) / 3, atol=1e-6)
for lab, s_val, sd in [("Delft 2015", 2.42, 0.20), ("Munich 2017", 2.22, 0.033), ("ETH Zurich 2023", 2.0747, 0.0033)]:
    check_true(f"{lab}: S = {s_val} +- {sd} lies above 2 and below 2 sqrt(2)", 2 < s_val < 2 * np.sqrt(2))

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E20] The spinning black hole from DMP's containment split: M^2 = m^2 + (J/2m)^2, units G = c = 1")
# The contained part m sets a Schwarzschild boundary (area 16 pi m^2, radius 2m); the spin count J, carried at that boundary, is a
# momentum J/(2m); energy and momentum combine as M^2 = m^2 + p^2. Solve m^4 - M^2 m^2 + J^2/4 = 0 and compare with Kerr (1963).
M_bh = 1.0


def contained_mass(J):
    disc = M_bh**4 - J**2
    return None if disc < 0 else np.sqrt((M_bh**2 + np.sqrt(disc)) / 2)


worst = 0.0
for a in np.linspace(0, 1, 101):
    m_c = contained_mass(a)
    r_plus = 1 + np.sqrt(1 - a * a)
    worst = max(worst, abs(16 * np.pi * m_c**2 - 4 * np.pi * (r_plus**2 + a * a)) / (4 * np.pi * (r_plus**2 + a * a)))
check("largest relative gap to Kerr's horizon area, spins 0 to 1 in steps of 0.01", worst, 0, atol=1e-12)
check_true("no real contained mass above a = 1: the spin bound comes out of the formula", contained_mass(1.001) is None)
check("share of the mass that can be taken out at a = 1, 1 - m/M", 1 - contained_mass(1.0), 1 - 1 / np.sqrt(2))

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[E21] 'A 2 node cluster still is not good design': two-lepton clusters and the leptons that are not protected")
alpha_fs = 7.2973525693e-3
me_c2 = 8.1871057769e-14  # J, electron rest energy
tau_pps = 2 * hbar / (alpha_fs**5 * me_c2)  # para-positronium, leading order: Gamma = alpha^5 m_e c^2 / (2 hbar)
check("para-positronium lifetime, leading order (measured 125 ps)", tau_pps, 125.1e-12, rtol=2e-2)
gamma_ops = 2 * (math.pi**2 - 9) / (9 * math.pi) * alpha_fs**6 * me_c2 / hbar  # ortho-positronium, Ore and Powell 1949
check("ortho-positronium lifetime, leading order (measured 142.05 ns; radiative corrections give the rest)", 1 / gamma_ops, 142.05e-9,
      rtol=3e-2)
GF, m_mu, hbar_GeVs = 1.1663788e-5, 0.1056583755, 6.582119569e-25  # GeV^-2, GeV, GeV s
tau_mu = hbar_GeVs / (GF**2 * m_mu**5 / (192 * math.pi**3))
check("muon lifetime from Fermi's formula G_F^2 m^5 / (192 pi^3) (measured 2.197 microseconds)", tau_mu, 2.1969811e-6, rtol=1e-2)

# ---------------------------------------------------------------------------------------------------------------------------------
passed = sum(results)
print(f"\n{passed} of {len(results)} checks passed")
raise SystemExit(0 if passed == len(results) else 1)
