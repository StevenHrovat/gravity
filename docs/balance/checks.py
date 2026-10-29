"""The Balanced State: the checks behind docs/balance/balance.tex.

Needs numpy. Runs in a second. Every printed line is a check with its expected value; the last line counts them. The paper stands on
these checks alone.

  [B1]  inflation as the possibility space: how many e-folds flatten an order-one curvature down to Planck's bound today
  [B2]  "it will eventually achieve equilibrium": the Hubble rate of flat LambdaCDM falls monotonically to sqrt(Omega_L) H0 (de Sitter)
  [B3]  "thus Shors algorithm": period finding for N = 15 on a simulated register; with interference it finds the period, with the
        register recorded (classical, commuting) it finds nothing
  [B4]  "the information a spinning bh leaks is it dragging Existence along": the ergosphere lies outside the horizon; Penrose and
        the extractable spin energy
  [B5]  "they can't just not Exist anymore, so they must leave something behind": every listed decay keeps charge, baryon number and
        lepton number, has at least two products and loses rest mass
  [B6]  "E(keep existing per h) = h*(1/c)*FSC": the dimension of the formula, and the two lengths alpha does relate to the electron
  [B7]  "at least two other things that must exist can witness it": in a baryon each quark's colour is fixed by the other two
  [B8]  "Must the Higgs field even exist in my system?": without a Higgs, W W scattering breaks unitarity below about 1 TeV
  [B9]  IM = strong + weak, GG = EM: the electromagnetic and weak couplings are one (sin^2 theta_W from G_F, m_W and alpha);
        the strong coupling reaches 1, and so 137 times alpha, only near the hadron scale
  [B10] the VIBE coefficient (formerly BSD), "how much Existence can interact with itself": the electron's self-interaction, its anomalous magnetic moment, is
        alpha / (2 pi) at first order (Schwinger) against the measured value
  [B11] "mass times length is the total amount of existence a space needs": m times the Compton wavelength is h/c for every particle,
        and alpha h / c is the electron's mass times the circumference of its classical radius
  [B12] "are they just constantly bouncing around between quarks?": how often gluons cross a proton
  [B13] the Higgs as pure existence that cannot exist alone: its lifetime, and why gravity cannot be what gives particles their mass
  [B14] "in the end it's all one field": the three Standard Model couplings approach each other at high energy but do not meet
  [B15] "137 times higher": the electromagnetic share of the proton's mass
  [B16] "the Higgs field [...] is indistinguishable [...] from G0 asserting Existence": if gravity weighed only the Higgs-given mass
        (electrons in full, about 9% of each nucleon, none of the nuclear binding), titanium and platinum would fall differently by
        about 1e-3; MICROSCOPE finds them equal to about 1e-15
  [B17] Lemma 1, Axiom 3's record: what every witness reads in full must be classical; one unitary copies two states only if their
        overlap is 0 or 1, and two non-commuting states cannot be broadcast
  [B18] Proposition 2, Axiom 1's "neither overrules the other": a scalar on the gravitational term (Brans-Dicke) moves gamma off 1;
        Cassini forces omega above 4e4
  [B19] Hawking-Penrose-Information radiation: the Hawking temperature of a solar-mass black hole, far below the 2.7 K sky
"""

import itertools
import math

import numpy as np

results = []


def check(label, got, want, rtol=1e-6, atol=0.0):
    got, want = float(got), float(want)
    ok = abs(got - want) <= max(atol, rtol * abs(want))
    print(f"{'OK  ' if ok else 'FAIL'} {label}: {got:.6g} (expected {want:.6g})")
    results.append(ok)


def check_true(label, cond):
    print(f"{'OK  ' if cond else 'FAIL'} {label}")
    results.append(bool(cond))


# Constants: SI 2019 exact values, CODATA 2018, PDG 2024, Planck 2018 (TT,TE,EE+lowE+lensing).
hbar = 1.054571817e-34      # J s
c = 299792458.0             # m/s
alpha = 7.2973525693e-3
m_e = 9.1093837015e-31      # kg
e_charge = 1.602176634e-19  # C
eps0 = 8.8541878128e-12     # F/m
G_F = 1.1663788e-5          # GeV^-2
m_W, m_Z, m_H = 80.369, 91.1876, 125.20  # GeV
alpha_mz_inv = 127.951
alpha_s_mz = 0.1180
Om, OL = 0.3153, 0.6847
Ok_bound = 0.004             # |Omega_k| < ~0.004 (Planck 2018, 95%, combined)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B1] 'Inflation is just the Possibility space of Existence': the flatness it buys")
# |Omega - 1| grows as a^2 in the radiation era and as a in the matter era. From a reheating temperature of 1e15 GeV to equality
# (T_eq = 0.80 eV, z_eq = 3400) and on to today it grows by (T_reh/T_eq)^2 (1 + z_eq); inflation shrinks it by e^(-2N).
T_reh, T_eq, z_eq = 1e15 * 1e9, 0.80, 3400.0   # eV
growth = (T_reh / T_eq) ** 2 * (1 + z_eq)
N_min = 0.5 * math.log(growth / Ok_bound)
print(f"     growth of |Omega - 1| since reheating: {growth:.2e}; e-folds needed from |Omega - 1| = 1: {N_min:.1f}")
check_true("an order-one curvature needs about 60 e-folds of inflation to meet Planck's bound (55 < N < 70)", 55 < N_min < 70)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B2] 'Currently it's at meh ... and will eventually achieve equilibrium': the late universe in flat LambdaCDM")


def hubble(z):
    return math.sqrt(Om * (1 + z) ** 3 + OL)


zs = np.linspace(5, -0.999, 2000)  # from the past (z = 5) into the far future (scale factor 1000)
H = [hubble(z) for z in zs]
check_true("the Hubble rate falls at every step from z = 5 into the far future", all(a > b for a, b in zip(H, H[1:])))
check("its limit, the de Sitter rate, as a share of today's: sqrt(Omega_L)", hubble(-0.999), math.sqrt(OL), rtol=1e-6)
z_t = (2 * OL / Om) ** (1 / 3) - 1
check("redshift at which deceleration turned into acceleration, (2 Omega_L/Omega_m)^(1/3) - 1", z_t, 0.6315, rtol=2e-3)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B3] 'thus Shors algorithm, thus universal QC': period finding for N = 15, a = 7")
N, a, n_bits = 15, 7, 8
Q = 2 ** n_bits
f = [pow(a, x, N) for x in range(Q)]
r = next(k for k in range(1, N) if pow(a, k, N) == 1)
# Coherent register: after computing f and measuring it, a QFT on the input register gives P(y).
p_coh = np.zeros(Q)
for z in set(f):
    xs = np.array([x for x in range(Q) if f[x] == z])
    amp = np.exp(2j * np.pi * np.outer(np.arange(Q), xs) / Q).sum(axis=1) / Q
    p_coh += np.abs(amp) ** 2
peaks = sorted(np.argsort(p_coh)[-r:])
check("period of 7^x mod 15", r, 4)
check("probability on the four peaks y = 0, 64, 128, 192 (interference)", p_coh[peaks].sum(), 1.0, rtol=1e-9)
check_true("the peaks are the multiples of Q/r", peaks == [0, 64, 128, 192])
check("the factors from the period: gcd(7^2 - 1, 15)", math.gcd(a ** (r // 2) - 1, N), 3)
check("and gcd(7^2 + 1, 15)", math.gcd(a ** (r // 2) + 1, N), 5)
# Recorded register: every witness holds x, so the register is diagonal (commuting); the QFT then spreads it uniformly.
F = np.exp(2j * np.pi * np.outer(np.arange(Q), np.arange(Q)) / Q) / math.sqrt(Q)
rho_rec = np.diag(np.full(Q, 1.0 / Q))  # dephased register: only the diagonal survives
p_rec = np.real(np.diag(F @ rho_rec @ F.conj().T))
check("largest probability with the register recorded in full (no peak, 1/Q)", p_rec.max(), 1 / Q, rtol=1e-12)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B4] 'Is the information a spinning bh leaks just it dragging Existence along?'  Units G = c = M = 1")
for spin in (0.5, 0.9, 1.0):
    r_plus = 1 + math.sqrt(1 - spin * spin)
    r_ergo = 2.0  # equatorial static limit, r = M + sqrt(M^2 - a^2 cos^2 theta) at theta = pi/2
    check_true(f"a = {spin}: the ergosphere (r = 2) lies outside the horizon (r+ = {r_plus:.3f})", r_ergo > r_plus)
    m_irr = math.sqrt(r_plus ** 2 + spin ** 2) / 2  # Christodoulou: M_irr = sqrt(A / 16 pi)
    print(f"     a = {spin}: spin energy frame dragging can give up, 1 - M_irr/M = {1 - m_irr:.4f}")
check("at a = 1 that share is 1 - 1/sqrt 2", 1 - math.sqrt(1 + 1) / 2, 1 - 1 / math.sqrt(2), rtol=1e-12)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B5] 'They can't just not Exist anymore, so they must leave something behind'")
# particle: (charge, baryon number, lepton number, mass in GeV)
P = {"mu-": (-1, 0, 1, 0.10566), "e-": (-1, 0, 1, 0.000511), "e+": (1, 0, -1, 0.000511), "nu": (0, 0, 1, 0.0),
     "nubar": (0, 0, -1, 0.0), "n": (0, 1, 0, 0.939565), "p": (1, 1, 0, 0.938272), "pi+": (1, 0, 0, 0.13957),
     "mu+": (1, 0, -1, 0.10566), "tau-": (-1, 0, 1, 1.77686), "pi-": (-1, 0, 0, 0.13957), "Z": (0, 0, 0, 91.1876),
     "W-": (-1, 0, 0, 80.369), "H": (0, 0, 0, 125.20), "gamma": (0, 0, 0, 0.0)}
DECAYS = [("mu-", ["e-", "nubar", "nu"]), ("n", ["p", "e-", "nubar"]), ("pi+", ["mu+", "nu"]), ("tau-", ["pi-", "nu"]),
          ("Z", ["e+", "e-"]), ("W-", ["e-", "nubar"]), ("H", ["gamma", "gamma"])]
for parent, kids in DECAYS:
    ok = (all(P[parent][i] == sum(P[k][i] for k in kids) for i in range(3)) and len(kids) >= 2
          and P[parent][3] > sum(P[k][3] for k in kids))
    check_true(f"{parent} -> {' '.join(kids)}: charge, baryon and lepton number kept, two or more products, rest mass lost", ok)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B6] 'E(keep existing per h) = h*(1/c)*FSC'")
dim = {"h": np.array([1, 2, -1]), "c": np.array([0, 1, -1]), "g": np.array([0, 1, -2])}  # (M, L, T)
energy = np.array([1, 2, -2])
check_true("h * (1/c) * alpha has dimension M L (a mass times a length), not an energy", tuple(dim["h"] - dim["c"]) == (1, 1, 0))
check_true("with the local field strength g it is an energy again: g h / c", tuple(dim["g"] + dim["h"] - dim["c"]) == tuple(energy))
lam_c = hbar / (m_e * c)
r_e = e_charge ** 2 / (4 * math.pi * eps0 * m_e * c ** 2)
a_0 = 4 * math.pi * eps0 * hbar ** 2 / (m_e * e_charge ** 2)
check("classical electron radius over the reduced Compton wavelength equals alpha", r_e / lam_c, alpha, rtol=1e-8)
check("reduced Compton wavelength over the Bohr radius equals alpha", lam_c / a_0, alpha, rtol=1e-8)
check("classical electron radius (m)", r_e, 2.8179403262e-15, rtol=1e-8)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B7] Baryons 'witnessed by at least two others': the colour singlet of three quarks")
eps = np.zeros((3, 3, 3))
for perm in itertools.permutations(range(3)):
    eps[perm] = np.linalg.det(np.eye(3)[list(perm)])
check_true("for every pair of different colours exactly one third colour completes the singlet",
           all(np.count_nonzero(eps[i, j, :]) == 1 for i in range(3) for j in range(3) if i != j))
rng = np.random.default_rng(1)
Zm = rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3))
U, _ = np.linalg.qr(Zm)
U = U / np.linalg.det(U) ** (1 / 3)  # special unitary
eps_rot = np.einsum("ia,jb,kc,abc->ijk", U, U, U, eps)
check("the singlet is unchanged by a random colour rotation (largest change)", np.abs(eps_rot - eps).max(), 0, atol=1e-12)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B8] 'Must the Higgs field even exist in my system?'")
lqt = math.sqrt(8 * math.pi * math.sqrt(2) / (3 * G_F))
check("Lee-Quigg-Thacker bound sqrt(8 pi sqrt2 / (3 G_F)) (GeV): above it, W W scattering breaks unitarity", lqt, 1008, rtol=2e-3)
check_true("the measured Higgs boson (125.2 GeV) sits below the bound, where the theory stays consistent", m_H < lqt)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B9] 'IM = strong + weak ... GG = EM'")
g2 = 8 * m_W ** 2 * G_F / math.sqrt(2)  # weak coupling from the Fermi constant
e2 = 4 * math.pi / alpha_mz_inv          # electromagnetic coupling at the Z mass
check("sin^2 theta_W = e^2 / g^2 from alpha(M_Z), G_F and m_W (measured 0.2312): EM and weak share one coupling", e2 / g2, 0.2312,
      rtol=2e-2)
b0 = 11 - 2 * 5 / 3
ln_mu2 = (1 - 1 / alpha_s_mz) * 4 * math.pi / b0
mu_one = m_Z * math.exp(ln_mu2 / 2)
check("strong over electromagnetic coupling at the Z mass", alpha_s_mz * alpha_mz_inv, 15.1, rtol=1e-2)
print(f"     one-loop scale where alpha_s reaches 1: {mu_one:.2f} GeV")
check_true("alpha_s reaches 1, and so 137 times alpha, only near the hadron scale (0.1 to 1 GeV)", 0.1 < mu_one < 1.0)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B10] 'the ratio of how much Existence can interact with itself, before it needs to reground itself'")
a_e_measured = 0.00115965218059  # Fan et al. 2023
check("the electron's anomalous magnetic moment at first order, alpha / (2 pi) (Schwinger), against the measured value",
      alpha / (2 * math.pi), a_e_measured, rtol=2e-3)
check("measured over first order (the rest is higher powers of alpha)", a_e_measured / (alpha / (2 * math.pi)), 0.99849, rtol=1e-4)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B11] 'mass times length is appropriate ... the total amount of existence that a space needs to generate to exist'")
h_planck = 2 * math.pi * hbar
# m * lambda_C = h / c holds by the definition of the Compton wavelength, for every particle; the check is the alpha identity below.
check("alpha h / c equals the electron mass times 2 pi r_e (circumference of the classical radius)", alpha * h_planck / c,
      m_e * 2 * math.pi * r_e, rtol=1e-8)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B12] 'How often are gluons currently supposed to interact?'")
r_p = 0.8409e-15  # proton charge radius (m)
t_cross = r_p / c
check("one light crossing of the proton (s)", t_cross, 2.805e-24, rtol=2e-3)
check_true("about 1e23 to 1e24 crossings per second, every second the proton exists", 1e23 < 1 / t_cross < 1e24)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B13] 'The Higgs boson would theoretically be all existence ... So it could not exist in isolation'")
hbar_GeVs = 6.582119569e-25
gamma_H = 4.1e-3  # GeV, Standard Model width at 125 GeV
check("Higgs boson lifetime hbar / Gamma (s)", hbar_GeVs / gamma_H, 1.605e-22, rtol=2e-3)
G = 6.67430e-11
v_ew = 246.22  # GeV, Higgs vacuum value
y_e = math.sqrt(2) * 0.51099895e-3 / v_ew
g_grav = G * m_e ** 2 / (hbar * c)
print(f"     electron: Higgs coupling y_e = {y_e:.2e}; gravitational coupling G m_e^2 / (hbar c) = {g_grav:.2e}")
check_true("gravity's coupling to the electron is more than 1e39 times weaker than the Higgs coupling that sets its mass",
           y_e / g_grav > 1e39)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B14] 'Since in the end it's all one field ... different tiers of IM'")
s2 = 0.23122
inv = [(3 / 5) * (1 - s2) * alpha_mz_inv, s2 * alpha_mz_inv, 1 / alpha_s_mz]  # 1/alpha_1 (GUT-normalised), 1/alpha_2, 1/alpha_3
bcoef = (41 / 10, -19 / 6, -7)
spreads = {}
for mu in (1e13, 1e14, 1e15, 1e16):
    L = math.log(mu / m_Z) / (2 * math.pi)
    vals = [x - b * L for x, b in zip(inv, bcoef)]
    spreads[mu] = max(vals) - min(vals)
    print(f"     {mu:.0e} GeV: 1/alpha_1,2,3 = {vals[0]:.1f}, {vals[1]:.1f}, {vals[2]:.1f}")
best = min(spreads, key=spreads.get)
check_true("the three inverse couplings come within about 10% of each other near 1e14 GeV", spreads[best] / 42 < 0.12 and best == 1e14)
check_true("but they never meet at one point in the Standard Model (smallest spread above 3)", min(spreads.values()) > 3)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B15] 'the existence derived from the internal affirmation ... is 130 times higher than the assertion from information'")
alpha_hbar_c_MeV_fm = 1.439964548  # e^2 / (4 pi eps0) in MeV fm
E_coul = 0.6 * alpha_hbar_c_MeV_fm / (r_p * 1e15)  # uniformly charged sphere of the proton's radius
share = E_coul / 938.272
print(f"     Coulomb self-energy of the proton {E_coul:.2f} MeV, share of its mass 1/{1 / share:.0f}")
check_true("the electromagnetic share of the proton's mass is about 1/1000, not 1/137", 700 < 1 / share < 1500)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B16] 'the Higgs field [...] is indistinguishable [...] from G0 asserting Existence': does gravity weigh only the Higgs share?")
# Atomic masses and binding from AME2020; the Higgs share of a nucleon's mass, the quark mass terms, is 9(2)% (Yang et al., PRL 121,
# 212001, 2018). Electrons get all their mass from the Higgs field, nuclear binding none. MICROSCOPE (Touboul et al., PRL 129, 121102,
# 2022): eta(Ti, Pt) = (-1.5 +- 2.3 stat +- 1.5 syst) e-15; we take 5e-15 as the bound.
u_MeV, me_MeV, mp_MeV, mn_MeV = 931.49410242, 0.51099895, 938.27208816, 939.56542052
atoms = {"Ti-48": (22, 48, 47.9479409), "Pt-195": (78, 195, 194.9647917)}
eta_bound = 5e-15
for f_N in (0.07, 0.09, 0.11):
    share = {k: (Z * me_MeV + f_N * (Z * mp_MeV + (A - Z) * mn_MeV)) / (M * u_MeV) for k, (Z, A, M) in atoms.items()}
    eta_pred = 2 * abs(share["Ti-48"] - share["Pt-195"]) / (share["Ti-48"] + share["Pt-195"])
    print(f"     nucleon Higgs share {f_N:.2f}: Higgs share Ti {share['Ti-48']:.5f}, Pt {share['Pt-195']:.5f}, predicted eta {eta_pred:.2e}")
    check_true(f"with a nucleon Higgs share of {f_N:.2f} the predicted eta exceeds MICROSCOPE's bound by more than 1e9", eta_pred > 1e9 * eta_bound)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B17] Lemma 1: 'a record ... that every witness of that act can read in full'. What can be read in full by two is classical")
# A record every witness holds in full is copied to each of them. One unitary U with U|s>|0> = |s>|s> for two states s, t preserves
# inner products, so <s|t> = <s|t>^2: the overlap is 0 or 1 (Wootters and Zurek 1982). For mixed states a set can be broadcast iff it
# commutes (Barnum et al. 1996).
ket0 = np.array([1.0, 0.0])
ket1 = np.array([0.0, 1.0])
ketp = np.array([1.0, 1.0]) / np.sqrt(2)
ov = float(ket0 @ ketp)
check("overlap of |0> and |+>", ov, 1 / np.sqrt(2))
check_true("<0|+> differs from <0|+>^2, so no unitary records both in full", abs(ov - ov**2) > 0.2)
for name, (u, v) in {"|0>, |1>": (ket0, ket1), "|0>, |0>": (ket0, ket0)}.items():
    o = float(u @ v)
    check_true(f"{name}: overlap {o:.0f} equals its square, a copier exists (a classical alphabet)", abs(o - o**2) < 1e-12)
rho_a, rho_b = np.outer(ket0, ket0), np.outer(ketp, ketp)
check("commutator norm of the two states (nonzero: the pair cannot be broadcast)", np.linalg.norm(rho_a @ rho_b - rho_b @ rho_a),
      1 / np.sqrt(2))

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B18] Proposition 2: a scalar that multiplies the gravitational term overrules the existence half; Cassini bounds it")
# Brans-Dicke: gamma = (1 + omega) / (2 + omega). Cassini: gamma - 1 = (2.1 +- 2.3) e-5 (Bertotti, Iess, Tortora 2003); 2 sigma below
# the central value is -2.5e-5.
omegas = np.array([1.0, 10.0, 1e3, 1e6, 1e9])
gam = (1 + omegas) / (2 + omegas)
check_true("Brans-Dicke gamma - 1 = -1/(omega + 2) for every omega tried", np.allclose(gam - 1, -1 / (omegas + 2), rtol=1e-6, atol=1e-15))
omega_min = 1 / 2.5e-5 - 2
check("smallest omega Cassini allows at 2 sigma", omega_min, 39998.0)
check_true("gamma tends to 1 as omega grows (Brans-Dicke reduces to general relativity)", abs(gam[-1] - 1) < 1e-8)

# ---------------------------------------------------------------------------------------------------------------------------------
print("\n[B19] 'Let's call it Hawking-Penrose-Information radiation': how cold the Hawking part is")
# T_H = hbar c^3 / (8 pi G M k_B) (Hawking 1975). CODATA 2018 G and k_B; IAU nominal solar mass parameter GM_sun = 1.3271244e20 m^3/s^2.
k_B = 1.380649e-23
GM_sun = 1.3271244e20
T_H = hbar * c**3 / (8 * math.pi * GM_sun * k_B)
print(f"     Hawking temperature of one solar mass: {T_H:.3g} K")
check("Hawking temperature of a solar-mass black hole (K)", T_H, 6.17e-8, rtol=0.01)
check_true("it is colder than the cosmic microwave background (2.725 K) by more than 1e7, so a real hole absorbs more than it emits",
           2.725 / T_H > 1e7)

# ---------------------------------------------------------------------------------------------------------------------------------
passed = sum(results)
print(f"\n{passed} of {len(results)} checks passed")
raise SystemExit(0 if passed == len(results) else 1)
