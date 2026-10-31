"""GUID v6: remnants with a history. The stochastic and the contained remnant of Section 11.6 against SPARC, with cosmic time included.

Run:  python3 docs/simulation/remnant_history.py --data <dir>     (or set SPARC_DATA_DIR=<dir>)
      <dir> holds MassModels_Lelli2016c.mrt and SPARC_Lelli2016c.mrt from http://astroweb.cwru.edu/SPARC/ (Lelli, McGaugh and
      Schombert, AJ 152, 157, 2016). The data are not part of this repository; their SHA256 is checked and the script stops if it differs.
Needs numpy, scipy, matplotlib. Deterministic: fixed seeds, BLAS on one thread, no clock, no machine name. Runs in about 2.5 minutes, under 200 MB.
Writes docs/simulation/results/remnant_history.{json,md} and docs/simulation/figures/remnant_{forms,scales,history,halos,redshift}.pdf.

It reuses the validated pipeline docs/simulation/sparc_rotation.py: constants, the SHA256 list, the readers, the RAR function and the
models are imported from it; the sample cuts, the error model of Lelli et al. (2017) and the likelihoods L1 and L2 live inside that
script's main() and are copied here, each copy marked "copied from sparc_rotation.py". Checks print OK or FAIL and the last line counts
them. The checks test pipeline reproduction and internal consistency only; every model comparison is a reported result, never a check.

Hypothesis and forms, fixed before any fit was run (the owner's proposal; a hypothesis, not a derivation):
  H-acc  The diffusion of the classical field leaves random kicks that accumulate over cosmic time as a random walk. If the variance
         of the extra acceleration grows with the local source g_bar and with time, its rms is a geometric mean of g_bar and an
         accumulated scale a_acc. Two forms, and only these two, are fitted:
           form B ("Brownian sum"):       g_obs = g_bar + sqrt(g_bar a_acc)
           form S ("self-consistent"):    (g_obs - g_bar) g_obs = g_bar a_acc,  i.e.  g_obs = g_bar/2 + sqrt(g_bar^2/4 + g_bar a_acc)
         (S: the excess is sourced by the total field it helps to make.) Both are known MOND phenomenology: S is Milgrom's "simple"
         interpolating function, B the plain sum of the Newtonian and the deep-MOND accelerations. Neither is derived from
         Oppenheim and Russo's calculation, which is static. The sqrt form was proposed after sparc_rotation.py had measured the
         residual slope 0.44 (a constant predicts 0, deep MOND 0.5), so its agreement with that slope is not a prediction.
  Natural scales for a_acc (the task's list, fixed before fitting): c H0, c H0/2 pi, c H_inf, c H_inf/2 pi with H_inf = sqrt(Omega_L) H0,
         each for H0 = 67.4 and 73 km/s/Mpc, and c/t0 with t0 = 13.8 Gyr: nine candidates.
  History proxies and the signs a galaxy-specific accumulation predicts (fixed before computing any correlation): older, more evolved
         systems accumulate more, so log a_i should fall with Hubble type T, fall with gas fraction, rise with surface brightness, fall
         with disk scale length, and rise with the number of orbits completed in a Hubble time, N_orb = t0 / (2 pi R_out / V_out)
         (variance growing by a fixed amount per orbit gives a_i proportional to N_orb, a log-log slope of 1).
  Evolution laws for R5 (fixed before comparison): a_acc constant; a_acc proportional to H(z); to 1/t; to t (random-walk
         accumulation: variance growing linearly with time gives a_acc proportional to t in form B).

  [S0] inputs: SHA256, readers (the extended reader for SBeff and Rdisk agrees with the validated one), 97 Hubble-flow distances
  [S1] pipeline reproduction: sample, points, the universal RAR and constant fits and the residual slope of sparc_rotation.py
  [R1] the accumulated stochastic remnant: (a) universal a_acc for B and S against the RAR, the constant and Newton (L1, L2, robust,
       galaxy bootstrap); the solar system; (b) the nine natural scales, with the look-elsewhere effect; (c) a_acc per galaxy
  [R2] history: rank correlations of per-galaxy a_acc, residuals and g+ with history proxies; galaxy bootstrap; Holm correction;
       mock universes (universal law + the SPARC error model) as the null for correlations made by shape mismatch and shared variables
  [R3] the contained remnant: baryons + NFW halo (Dutton and Maccio 2014 c-M prior; and with the Moster, Naab and White 2013
       stellar-to-halo mass relation as a cosmological-halo prior) and Burkert halos, per galaxy, against the universal laws
  [R4] the whole: baryons + halo + one universal stochastic term (constant or sqrt form): profile likelihood, 95% upper bound, room left
  [R5] cosmic time: a_acc(z) laws against published high-redshift kinematics (verified numbers only)
"""

import os

for _v in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"   # deterministic BLAS and no oversubscription on a shared machine

import argparse  # noqa: E402
import json  # noqa: E402
import math  # noqa: E402
import sys  # noqa: E402
import warnings  # noqa: E402
from pathlib import Path  # noqa: E402

import numpy as np  # noqa: E402
from scipy import integrate, optimize, stats  # noqa: E402

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import sparc_rotation as SR  # noqa: E402  (the validated pipeline)

RESULTS, FIGURES = SR.RESULTS, SR.FIGURES
SEED = SR.SEED
N_BOOT = 1000
N_MOCK = 500

c, G, M_sun, kpc, Mpc, LOG10 = SR.c, SR.G, SR.M_sun, SR.kpc, SR.Mpc, SR.LOG10
G_KPC, UPS_D, UPS_B, HE_GAS = SR.G_KPC, SR.UPS_D, SR.UPS_B, SR.HE_GAS
OMEGA_L = SR.Omega_L                    # 0.685 (Planck 2018, as in checks.py)
OMEGA_M = 1.0 - OMEGA_L                 # 0.315, flat
H0_PL = 67.4e3 / Mpc                    # Planck 2018
H0_SH = 73.0e3 / Mpc                    # the H0 of SPARC's Hubble-flow distances (Lelli et al. 2016)
YEAR = 365.25 * 86400.0
GYR = 1e9 * YEAR
T0_TASK = 13.8 * GYR
AU = 1.495978707e11
GM_SUN = G * M_sun
H_LITTLE = 0.674
RHO_C = 3 * (67.4e-3) ** 2 / (8 * math.pi * G_KPC)      # critical density, Msun/kpc^3 (H in km/s/kpc)

# Published numbers, each checked against the paper's text on 2026-10-31 (see the references in the summary).
DM14 = dict(a=0.905, b=-0.101, sigma=0.11)      # Dutton & Maccio 2014, Eq. 8: log c200 = a + b log(M200 / 1e12 h^-1 Msun), z = 0
MNW13 = dict(logM1=11.590, N=0.0351, beta=1.376, gamma=0.608, sigma=0.15)   # Moster, Naab & White 2013, Eq. 2, Table 1 (z = 0)
PITJEVA = {"Mercury": (-0.020, 0.030), "Venus": (0.026, 0.016), "Earth": (0.0019, 0.0019), "Mars": (-0.00020, 0.00037),
           "Jupiter": (0.587, 0.283), "Saturn": (-0.0032, 0.0047)}   # Pitjeva & Pitjev 2013, Table 4: extra perihelion precession, mas/yr
PLANETS = {"Mercury": (0.3871, 0.2408), "Venus": (0.7233, 0.6152), "Earth": (1.0000, 1.0000), "Mars": (1.5237, 1.8808),
           "Jupiter": (5.2034, 11.862), "Saturn": (9.5371, 29.457)}  # semi-major axis [AU], period [yr]; rounded standard elements
UBLER17 = dict(z=[0.9, 2.3], db=[-0.44, -0.27], db_err=[0.04, 0.05], db_no_pressure=[-0.33, -0.09], n=[65, 46], slope=3.75)
MUSEDARK = dict(z_lo=0.33, z_hi=1.44, n=79, a0_z1=2.38e-10, a0_z1_lo=0.10e-10, a0_z1_hi=0.12e-10, a0_0_fit=1.0e-10, a0_0_fit_err=0.04e-10,
                a1=1.59e-10, a1_err=0.10e-10, a0_local=1.2e-10, a0_local_err=0.26e-10)
RC100 = dict(fdm=[0.38, 0.27], fdm_scatter=[0.23, 0.18], zbin=[[0.6, 1.2], [1.2, 2.5]], n=[33, 67])

# Values of the validated run of sparc_rotation.py (results/sparc_rotation.json) that this script must reproduce.
REF = dict(n_gal=153, n_pts=2696, n_gal_pts=147, rar_best=1.11922e-10, rar_m2lnL=-2462.28, const_best=2.26882e-11, const_m2lnL=2603.56,
           newton_m2lnL=50190.6, slope_low=0.436365, n_gal5=132)

results, check_log = [], []


def check(label, got, want, rtol=1e-6, atol=0.0):
    got, want = float(got), float(want)
    ok = abs(got - want) <= max(atol, rtol * abs(want))
    print(f"{'OK  ' if ok else 'FAIL'} {label}: {got:.6g} (expected {want:.6g})")
    results.append(ok)
    check_log.append({"label": label, "ok": ok, "got": got, "want": want})


def check_true(label, cond):
    print(f"{'OK  ' if cond else 'FAIL'} {label}")
    results.append(bool(cond))
    check_log.append({"label": label, "ok": bool(cond)})


# ---------------------------------------------------------------------------------------------------------------------------------
# Models. Each returns (log10 g_model, d log g_model / d log g_bar), the signature of sparc_rotation.py.

def m_brown(theta, gb, _R=None):
    a = 10.0 ** theta[0]
    s = np.sqrt(gb * a)
    g = gb + s
    return np.log10(g), (gb + 0.5 * s) / g


def m_simple(theta, gb, _R=None):
    a = 10.0 ** theta[0]
    g = 0.5 * gb + np.sqrt(0.25 * gb * gb + gb * a)
    return np.log10(g), gb * (g + a) / (g * (2 * g - gb))


MODELS = {"newton": SR.m_newton, "rar": SR.m_rar, "const": SR.m_guid, "brown": m_brown, "simple": m_simple}
LABEL = {"newton": "Newton (g_bar only)", "rar": "RAR (McGaugh et al. 2016 function)", "const": "constant |γ1|/2 (sparc_rotation.py)",
         "brown": "form B: g_bar + √(g_bar a_acc)", "simple": "form S: g_bar/2 + √(g_bar²/4 + g_bar a_acc)"}


def g_lin(kind, gb, a):
    """The model acceleration in m/s^2 (no Lambda term)."""
    if kind == "rar":
        return SR.F_rar(gb, a)
    if kind == "const":
        return gb + a
    if kind == "brown":
        return gb + np.sqrt(gb * a)
    if kind == "simple":
        return 0.5 * gb + np.sqrt(0.25 * gb * gb + gb * a)
    return gb


TGRID = np.round(np.arange(-13.0, -7.99999, 0.01), 4)       # log10 of a per-galaxy scale (a_acc or g+)
AGRID = 10.0 ** TGRID


def parabola(ch, k, step):
    """Vertex of the parabola through ch[k-1], ch[k], ch[k+1] (offset in units of the grid, minimum value)."""
    den = ch[k - 1] - 2 * ch[k] + ch[k + 1]
    if den <= 0:
        return 0.0, ch[k]
    d = 0.5 * (ch[k - 1] - ch[k + 1]) / den
    return d * step, ch[k] - 0.25 * (ch[k - 1] - ch[k + 1]) * d


def grid_models(kind, gb):
    """Model g and log slope on TGRID for every point: arrays (n, len(TGRID))."""
    gb2 = gb[:, None]
    A = AGRID[None, :]
    with np.errstate(over="ignore", invalid="ignore", divide="ignore"):
        if kind == "brown":
            s = np.sqrt(gb2 * A)
            g = gb2 + s
            sl = (gb2 + 0.5 * s) / g
        elif kind == "simple":
            g = 0.5 * gb2 + np.sqrt(0.25 * gb2 * gb2 + gb2 * A)
            sl = gb2 * (g + A) / (g * (2 * g - gb2))
        elif kind == "rar":
            u = np.sqrt(gb2 / A)
            g = gb2 / (-np.expm1(-u))
            sl = 1 - (u / 2) / np.expm1(u)
            sl = np.where(np.isfinite(sl), sl, 1.0)
        else:
            raise ValueError(kind)
    return g, sl


def grid_fit_chi2(kind, gb, yv, sv):
    """One scale per galaxy, chi^2 with the velocity errors only (as sparc_rotation.py S2c): best log a, chi2 min, chi2 curve, at edge."""
    g, _ = grid_models(kind, gb)
    ch = np.sum(((yv[:, None] - np.log10(g)) / sv[:, None]) ** 2, axis=0)
    k = int(np.argmin(ch))
    if 0 < k < len(TGRID) - 1:
        d, cm = parabola(ch, k, 0.01)
        return TGRID[k] + d, cm, ch, False
    return TGRID[k], ch[k], ch, True


def grid_fit_l1(kind, gd):
    """One scale per galaxy with the L1 likelihood (full error model): best log a and -2 ln L at the best."""
    g, sl = grid_models(kind, gd["gb"])
    var = gd["so2"][:, None] + sl * sl * gd["sb2"][:, None]
    r = gd["y"][:, None] - np.log10(g)
    m2l = np.sum(r * r / var + np.log(2 * np.pi * var), axis=0)
    k = int(np.argmin(m2l))
    if 0 < k < len(TGRID) - 1:
        d, mm_ = parabola(m2l, k, 0.01)
        return TGRID[k] + d, mm_
    return TGRID[k], m2l[k]


# ---------------------------------------------------------------------------------------------------------------------------------
# Halos (the contained remnant). Radii in kpc, accelerations in m/s^2.

def mu_nfw(u):
    return np.log1p(u) - u / (1 + u)


def halo_menc(kind, R, p1, p2):
    """Enclosed halo mass [Msun]. NFW: p1 = log M200 [Msun], p2 = log c200. Burkert: p1 = log rho0 [Msun/kpc^3], p2 = log r0 [kpc]."""
    if kind == "burkert":
        rho0, r0 = 10.0 ** p1, 10.0 ** p2
        xx = R / r0
        return math.pi * rho0 * r0 ** 3 * (np.log1p(xx * xx) + 2 * np.log1p(xx) - 2 * np.arctan(xx))
    M, cc = 10.0 ** p1, 10.0 ** p2
    r200 = np.cbrt(3 * M / (800 * math.pi * RHO_C))
    return M * mu_nfw(cc * R / r200) / mu_nfw(cc)


def g_halo(kind, R, p1, p2):
    return G_KPC * halo_menc(kind, R, p1, p2) / R ** 2 * 1e6 / kpc


def lmstar_mnw13(lM):
    M = 10.0 ** lM
    q = M / 10.0 ** MNW13["logM1"]
    return np.log10(2 * MNW13["N"] * M / (q ** -MNW13["beta"] + q ** MNW13["gamma"]))


def halo_prior(kind, p1, p2, lmstar):
    """-2 ln prior: the c-M relation of Dutton & Maccio (2014) for NFW; plus the Moster et al. (2013) SHMR for nfw_shmr; none for Burkert."""
    if kind == "burkert":
        return 0.0 * p1
    pr = ((p2 - (DM14["a"] + DM14["b"] * (p1 + math.log10(H_LITTLE) - 12))) / DM14["sigma"]) ** 2
    if kind == "nfw_shmr":
        pr = pr + ((lmstar - lmstar_mnw13(p1)) / MNW13["sigma"]) ** 2
    return pr


HBOUNDS = {"nfw": ((8.0, 14.5), (0.0, 2.0)), "burkert": ((4.0, 10.5), (-1.0, 2.7))}
_g1 = {"nfw": np.arange(8.0, 14.5001, 0.15), "burkert": np.arange(4.0, 10.5001, 0.15)}
_g2 = {"nfw": np.arange(0.0, 2.0001, 0.1), "burkert": np.arange(-1.0, 2.7001, 0.1)}
HGRID = {k: tuple(a.ravel() for a in np.meshgrid(_g1[k], _g2[k], indexing="ij")) for k in _g1}


def extra_term(skind, gb, A):
    """The universal stochastic term and d(term)/d ln g_bar: none, constant A, or sqrt(g_bar A)."""
    if skind == "none" or A <= 0:
        return 0.0 * gb, 0.0 * gb
    if skind == "const":
        return A + 0.0 * gb, 0.0 * gb
    s = np.sqrt(gb * A)
    return s, 0.5 * s


def fit_halo(kind, gd, skind="none", A=0.0):
    """Per-galaxy MAP fit of a two-parameter halo (plus a fixed universal term): params, -2 ln (L prior), -2 ln L."""
    base = "burkert" if kind == "burkert" else "nfw"
    (lo1, hi1), (lo2, hi2) = HBOUNDS[base]
    gb, R_, yv, so2, sb2 = gd["gb"], gd["R"], gd["y"], gd["so2"], gd["sb2"]
    ex, dex = extra_term(skind, gb, A)
    P1, P2 = HGRID[base]
    gm = (gb + ex)[:, None] + g_halo(base, R_[:, None], P1[None, :], P2[None, :])
    sl = (gb + dex)[:, None] / gm
    var = so2[:, None] + sl * sl * sb2[:, None]
    r = yv[:, None] - np.log10(gm)
    obj = np.sum(r * r / var + np.log(2 * np.pi * var), axis=0) + halo_prior(kind, P1, P2, gd["lmstar"])
    k = int(np.argmin(obj))

    def parts(p):
        g_ = gb + ex + g_halo(base, R_, p[0], p[1])
        s_ = (gb + dex) / g_
        v_ = so2 + s_ * s_ * sb2
        r_ = yv - np.log10(g_)
        m2l = float(np.sum(r_ * r_ / v_ + np.log(2 * np.pi * v_)))
        return m2l + float(halo_prior(kind, p[0], p[1], gd["lmstar"])), m2l

    def f(p):
        if not (lo1 <= p[0] <= hi1 and lo2 <= p[1] <= hi2):
            return 1e30
        return parts(p)[0]

    x0 = np.array([P1[k], P2[k]])
    simplex = np.array([x0, x0 + [0.1 if x0[0] + 0.1 <= hi1 else -0.1, 0.0], x0 + [0.0, 0.1 if x0[1] + 0.1 <= hi2 else -0.1]])
    res = optimize.minimize(f, x0, method="Nelder-Mead", options={"xatol": 1e-4, "fatol": 1e-4, "maxfev": 600, "initial_simplex": simplex})
    p = res.x if res.fun <= obj[k] else x0
    pen, m2l = parts(p)
    return [float(p[0]), float(p[1])], pen, m2l


# ---------------------------------------------------------------------------------------------------------------------------------
# Statistics helpers.

def holm(p):
    p = np.asarray(p, float)
    order = np.argsort(p)
    m = len(p)
    adj = np.empty(m)
    run = 0.0
    for rank, i in enumerate(order):
        run = max(run, min(1.0, (m - rank) * p[i]))
        adj[i] = run
    return adj


def spearman(a, b):
    r = stats.spearmanr(a, b)
    return float(r.statistic), float(r.pvalue)


def partial_spearman(a, b, z):
    """Spearman correlation of a and b with the ranks of z regressed out (linear in ranks); p from t with n - 3 dof."""
    ra, rb, rz = stats.rankdata(a), stats.rankdata(b), stats.rankdata(z)
    zc = rz - rz.mean()

    def res(u):
        uc = u - u.mean()
        return uc - (uc @ zc) / (zc @ zc) * zc

    ea, eb = res(ra), res(rb)
    r = float(ea @ eb / math.sqrt((ea @ ea) * (eb @ eb)))
    n = len(a)
    t = r * math.sqrt((n - 3) / max(1e-300, 1 - r * r))
    return r, float(2 * stats.t.sf(abs(t), n - 3))


def scatter_ml(l, s):
    """Maximum-likelihood intrinsic scatter tau of values l with errors s (Gaussian): tau, 68% range, Delta(-2 ln L) of tau = 0."""
    taus = np.linspace(0.0, 1.0, 2001)

    def prof(tau):
        w = 1 / (s * s + tau * tau)
        mu = np.sum(w * l) / np.sum(w)
        return float(np.sum(w * (l - mu) ** 2) - np.sum(np.log(w))), float(mu)

    P = np.array([prof(t)[0] for t in taus])
    k = int(np.argmin(P))
    ok = P <= P[k] + 1
    return float(taus[k]), [float(taus[np.argmax(ok)]), float(taus[len(ok) - 1 - np.argmax(ok[::-1])])], float(P[0] - P[k]), prof(taus[k])[1]


def tau_fast(l, s):
    """Maximum-likelihood intrinsic scatter on a 0.0025-dex grid (vectorised version of scatter_ml, for the mocks)."""
    taus = np.linspace(0.0, 1.5, 601)[:, None]
    W = 1 / (s[None, :] ** 2 + taus ** 2)
    mu = np.sum(W * l[None, :], axis=1, keepdims=True) / np.sum(W, axis=1, keepdims=True)
    P = np.sum(W * (l[None, :] - mu) ** 2, axis=1) - np.sum(np.log(W), axis=1)
    return float(taus[int(np.argmin(P)), 0])


def E_of_z(z):
    return math.sqrt(OMEGA_M * (1 + z) ** 3 + OMEGA_L)


def t_of_z(z, H0=H0_PL):
    """Age at redshift z in flat LCDM without radiation (Omega_m = 0.315, Omega_L = 0.685)."""
    return 2 / (3 * H0 * math.sqrt(OMEGA_L)) * math.asinh(math.sqrt(OMEGA_L / OMEGA_M) * (1 + z) ** -1.5)


LAWS = {"constant": lambda z: 1.0, "H(z)": E_of_z, "1/t": lambda z: t_of_z(0) / t_of_z(z), "t (accumulation)": lambda z: t_of_z(z) / t_of_z(0)}


def db_regime(ratio, x0, gd0):
    """Delta log M_bar at fixed V and R for a RAR-shaped law whose scale changes by `ratio`: g_obs = x0 g+(0) held fixed."""
    gobs = x0 * gd0

    def gbar(gd):
        return optimize.brentq(lambda lg: math.log(SR.F_rar(math.exp(lg), gd)) - math.log(gobs), math.log(gobs) - 60, math.log(gobs),
                               xtol=1e-13)

    return (gbar(gd0 * ratio) - gbar(gd0)) / LOG10


def precession_numeric(n, eps, ecc=0.02):
    """Apsidal advance per radial period for a force GM/r^2 + k r^n (GM = 1), k set so that k r_g^n / (1/r_g^2) = eps at the guiding radius."""
    r0, vt = 1.0, 1.0 * (1 + ecc / 2)
    # guiding radius r_g: L^2 = F(r_g) r_g^3, with F(r) = 1/r^2 + k r^n and k = eps r_g^(-2-n): F(r_g) r_g^3 = r_g (1 + eps)
    L = r0 * vt
    rg = L * L / (1 + eps)
    k = eps * rg ** (-2 - n)

    def rhs(_t, s):
        x_, y_, vx, vy = s
        r = math.hypot(x_, y_)
        F = 1 / r ** 2 + k * r ** n
        return [vx, vy, -F * x_ / r, -F * y_ / r]

    def peri(_t, s):
        return s[0] * s[2] + s[1] * s[3]

    peri.direction = 1.0
    sol = integrate.solve_ivp(rhs, (0, 80 * math.pi), [r0, 0.0, 0.0, vt], method="DOP853", rtol=1e-12, atol=1e-12, events=peri)
    ang = np.array([math.atan2(s[1], s[0]) for s in sol.y_events[0]])
    adv = (np.diff(ang) + math.pi) % (2 * math.pi) - math.pi        # advance per radial period, mapped to (-pi, pi]
    return float(np.mean(adv)), -math.pi * (n + 2) * eps


# ---------------------------------------------------------------------------------------------------------------------------------
# Inputs.

def read_extra(path):
    """The galaxy table with the columns sparc_rotation.read_galaxies drops (SBeff, Rdisk, SBdisk); same token rules."""
    lines = path.read_text(encoding="ascii").splitlines()
    out = {}
    for line in SR.data_lines(lines):
        tok = line.split()
        if len(tok) != 19 or not SR.NAME_RE.match(tok[0]):
            raise SystemExit(f"FAIL unexpected galaxy-table line: {line[:80]!r}")
        v = [float(t) for t in tok[1:18]]
        out[tok[0]] = dict(T=int(v[0]), D=v[1], fD=int(v[3]), Inc=v[4], L=v[6], Reff=v[8], SBeff=v[9], Rdisk=v[10], SBdisk=v[11],
                           MHI=v[12], Vflat=v[14], Q=int(v[16]))
    return out


class Sparc:
    def __init__(self, ddir):
        print("\n[S0] Inputs: SPARC (Lelli, McGaugh and Schombert 2016), checked by SHA256 before anything is read")
        self.hashes = {}
        for name, want in SR.FILES.items():
            p = ddir / name
            if not p.is_file():
                raise SystemExit(f"FAIL missing input file {p}")
            got = SR.sha256(p)
            if got != want:
                raise SystemExit(f"FAIL SHA256 of {name} is {got}, expected {want}")
            self.hashes[name] = got
            check_true(f"SHA256 of {name} matches {want[:16]}...", True)
        _, mm = SR.read_mass_models(ddir / "MassModels_Lelli2016c.mrt")
        _, gal = SR.read_galaxies(ddir / "SPARC_Lelli2016c.mrt")
        ext = read_extra(ddir / "SPARC_Lelli2016c.mrt")
        self.mm, self.gal, self.ext = mm, gal, ext
        check("galaxies in the galaxy table", len(gal), 175, rtol=0)
        check("galaxies in the mass-model table", len({r[0] for r in mm}), 175, rtol=0)
        same = set(ext) == set(gal) and all(ext[n][k] == gal[n][k] for n in gal for k in ("T", "D", "fD", "Inc", "L", "Reff", "MHI", "Vflat", "Q"))
        check_true("the extended reader (SBeff, Rdisk) agrees with sparc_rotation.read_galaxies on every shared field", same)
        n_hf = sum(1 for n in gal if gal[n]["fD"] == 1)
        check("galaxies with Hubble-flow distances, f_D = 1 (SPARC paper: 97, on H0 = 73)", n_hf, 97, rtol=0)

        print("\n[S1] The validated sample and error model (copied from sparc_rotation.py, S1)")
        sample = sorted(n for n in gal if gal[n]["Q"] < 3 and gal[n]["Inc"] >= 30)
        ins = set(sample)
        pts = [r for r in mm if r[0] in ins and r[4] / r[3] < 0.1]
        check("galaxies in the RAR sample (sparc_rotation.py: 153)", len(sample), REF["n_gal"], rtol=0)
        check("points with dV/V < 0.1 (sparc_rotation.py: 2696)", len(pts), REF["n_pts"], rtol=0)
        self.gname = np.array([r[0] for r in pts])
        D = np.array([r[1] for r in pts])
        self.R = np.array([r[2] for r in pts])
        V = np.array([r[3] for r in pts])
        eV = np.array([r[4] for r in pts])
        Vg, Vd, Vb = (np.array([r[k] for r in pts]) for k in (5, 6, 7))
        self.inc = np.array([gal[n]["Inc"] for n in self.gname])
        einc = np.array([gal[n]["eInc"] for n in self.gname])
        eD = np.array([gal[n]["eD"] for n in self.gname])
        self.fD = np.array([gal[n]["fD"] for n in self.gname])
        self.g_obs = SR.kms2_per_kpc_to_si(V ** 2 / self.R)
        self.g_gas = SR.kms2_per_kpc_to_si(Vg * np.abs(Vg) / self.R)
        self.g_star = SR.kms2_per_kpc_to_si((UPS_D * Vd * np.abs(Vd) + UPS_B * Vb * np.abs(Vb)) / self.R)
        self.g_bar = self.g_gas + self.g_star
        # copied from sparc_rotation.py: Lelli et al. (2017) Eq. 2 and Sect. 2.1.2
        self.s_V = 2 * eV / V / LOG10
        s_incD = np.sqrt((2 * np.radians(einc) / np.tan(np.radians(self.inc))) ** 2 + (eD / D) ** 2) / LOG10
        s_obs = np.sqrt(self.s_V ** 2 + s_incD ** 2)
        s_bar = np.sqrt((0.10 * self.g_gas) ** 2 + (0.25 * self.g_star) ** 2) / self.g_bar / LOG10
        self.so2, self.sb2 = s_obs ** 2, s_bar ** 2
        self.x, self.y = np.log10(self.g_bar), np.log10(self.g_obs)
        self.N = len(self.y)
        self.gal_list = sorted(set(self.gname))
        self.gal_idx = [np.flatnonzero(self.gname == n) for n in self.gal_list]
        self.pt_gal = np.empty(self.N, int)
        for k, gi in enumerate(self.gal_idx):
            self.pt_gal[gi] = k
        check("galaxies contributing points (sparc_rotation.py: 147)", len(self.gal_list), REF["n_gal_pts"], rtol=0)
        check_true("g_bar > 0 at every selected point", bool(np.all(self.g_bar > 0)))
        # per galaxy (of the 147)
        self.eD_rel = np.array([gal[n]["eD"] / gal[n]["D"] for n in self.gal_list])
        self.einc_g = np.array([gal[n]["eInc"] for n in self.gal_list])
        self.Mbar = np.array([1e9 * (UPS_D * gal[n]["L"] + HE_GAS * gal[n]["MHI"]) for n in self.gal_list])
        self.lmstar = np.array([math.log10(1e9 * UPS_D * gal[n]["L"]) for n in self.gal_list])
        self.fgas = np.array([HE_GAS * gal[n]["MHI"] * 1e9 for n in self.gal_list]) / self.Mbar
        self.T = np.array([gal[n]["T"] for n in self.gal_list], float)
        self.SBeff = np.array([ext[n]["SBeff"] for n in self.gal_list])
        self.Rdisk = np.array([ext[n]["Rdisk"] for n in self.gal_list])
        rows_by = {}
        for r in mm:
            rows_by.setdefault(r[0], []).append(r)
        outer = [max(rows_by[n], key=lambda q: q[2]) for n in self.gal_list]
        self.Rout = np.array([o[2] for o in outer])
        self.Vout = np.array([o[3] for o in outer])
        self.Norb = T0_TASK / (2 * math.pi * self.Rout * kpc / (self.Vout * 1e3))
        self.all_idx = np.arange(self.N)

    def arrays(self, ups=1.0, dy=None):
        """(g_bar, y, so2, sb2) with the stellar M/L scaled by ups and log g_obs shifted by dy (per point)."""
        if ups == 1.0 and dy is None:
            return self.g_bar, self.y, self.so2, self.sb2
        gb = self.g_gas + ups * self.g_star
        sb = np.sqrt((0.10 * self.g_gas) ** 2 + (0.25 * ups * self.g_star) ** 2) / gb / LOG10
        return gb, (self.y if dy is None else self.y + dy), self.so2, sb * sb

    # Likelihood L1 (copied from sparc_rotation.py): Gaussian in log10 g_obs, variance = full error model with the g_bar error carried
    # through the model's slope; -2 ln L = sum r^2/var + ln(2 pi var).
    def nll1(self, model, theta, idx, arr=None):
        gb, yv, so2, sb2 = arr if arr is not None else (self.g_bar, self.y, self.so2, self.sb2)
        m, s = model(theta, gb[idx], self.R[idx])
        var = so2[idx] + s * s * sb2[idx]
        r = yv[idx] - m
        return float(np.sum(r * r / var + np.log(2 * np.pi * var))), float(np.sum(r * r / var))

    def fit1(self, model, lo, hi, idx, arr=None):
        res = optimize.minimize_scalar(lambda t: self.nll1(model, [t], idx, arr)[0], bounds=(lo, hi), method="bounded",
                                       options={"xatol": 1e-7})
        return float(res.x), float(res.fun)

    # Likelihood L2 (copied from sparc_rotation.py): velocity errors plus a free intrinsic floor.
    def fit2(self, model, p0):
        idx = self.all_idx

        def nll2(theta, lsig):
            m, _ = model(theta, self.g_bar[idx], self.R[idx])
            var = self.s_V[idx] ** 2 + (10.0 ** lsig) ** 2
            r = self.y[idx] - m
            return float(np.sum(r * r / var + np.log(2 * np.pi * var)))

        if model is SR.m_newton:
            res = optimize.minimize_scalar(lambda ls: nll2([], ls), bounds=(-3, 0), method="bounded", options={"xatol": 1e-7})
            return None, float(10 ** res.x), float(res.fun)
        res = optimize.minimize(lambda q: nll2(q[:-1], q[-1]), list(p0) + [-1.0], method="Nelder-Mead",
                                options={"xatol": 1e-7, "fatol": 1e-7, "maxiter": 4000})
        return float(res.x[0]), float(10 ** res.x[-1]), float(res.fun)

    # Robust variant (copied from sparc_rotation.py): soft-L1 loss on the L1 residuals, scatter as 1.4826 MAD.
    def robust(self, model, p0):
        idx = self.all_idx

        def resid(q):
            m, s = model(q, self.g_bar[idx], self.R[idx])
            return (self.y[idx] - m) / np.sqrt(self.so2[idx] + s ** 2 * self.sb2[idx])

        res = optimize.least_squares(resid, p0, loss="soft_l1", f_scale=1.0, x_scale=1.0, xtol=1e-12, ftol=1e-12)
        m, _ = model(res.x, self.g_bar[idx], self.R[idx])
        r = self.y[idx] - m
        return float(res.x[0]), float(1.4826 * np.median(np.abs(r - np.median(r))))

    def boot_idx(self, rng):
        pick = rng.integers(0, len(self.gal_idx), len(self.gal_idx))
        return np.concatenate([self.gal_idx[k] for k in pick])

    def gal_data(self, k, y=None):
        gi = self.gal_idx[k]
        return dict(gb=self.g_bar[gi], R=self.R[gi], y=(self.y if y is None else y)[gi], so2=self.so2[gi], sb2=self.sb2[gi],
                    sV=self.s_V[gi], lmstar=self.lmstar[k], gi=gi)


BOUNDS = {"rar": (-11.0, -9.0), "const": (-13.0, -8.5), "brown": (-12.5, -9.0), "simple": (-12.5, -9.0)}


def binned_slope(S, dg, low_cut, model_dg=None):
    """The low-acceleration slope of log(Delta g) against log g_bar in 0.3-dex bins (copied from sparc_rotation.py S2d)."""
    bins = np.arange(-12.3, -8.39, 0.3)
    out = []
    for lo_, hi_ in zip(bins[:-1], bins[1:]):
        sel = (S.x >= lo_) & (S.x < hi_)
        if sel.sum() >= 15:
            out.append((float(np.median(S.x[sel])), float(np.median(dg[sel]))))
        else:
            out.append((np.nan, np.nan))
    B = np.array(out)
    ok = (B[:, 0] < math.log10(low_cut)) & (B[:, 1] > 0)
    sl = float(np.polyfit(B[ok, 0], np.log10(B[ok, 1]), 1)[0])
    if model_dg is None:
        return sl, B, ok
    md = model_dg(10 ** B[ok, 0])
    return sl, float(np.polyfit(B[ok, 0], np.log10(md), 1)[0])


# ---------------------------------------------------------------------------------------------------------------------------------

def main():
    warnings.filterwarnings("ignore", message="All-NaN slice encountered", category=RuntimeWarning)
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--data", default=os.environ.get("SPARC_DATA_DIR"), help="directory with the two SPARC .mrt files")
    ap.add_argument("--boot", type=int, default=N_BOOT, help="bootstrap resamples (galaxies drawn with replacement)")
    ap.add_argument("--mock", type=int, default=N_MOCK, help="mock universes per null model in R2")
    ap.add_argument("--no-figures", action="store_true")
    args = ap.parse_args()
    if not args.data:
        raise SystemExit("FAIL no data directory: pass --data <dir> or set SPARC_DATA_DIR")
    S = Sparc(Path(args.data))
    allidx, N, lnN = S.all_idx, S.N, math.log(S.N)
    o = {"script": "docs/simulation/remnant_history.py", "seed": SEED, "n_boot": args.boot, "n_mock": args.mock,
         "inputs": {"files": {k: {"sha256": v} for k, v in S.hashes.items()},
                    "source": "Lelli, McGaugh, Schombert, AJ 152, 157 (2016); http://astroweb.cwru.edu/SPARC/"},
         "sample": {"n_galaxies": REF["n_gal"], "n_points": N, "n_galaxies_with_points": len(S.gal_list)}}

    # ===========================================================================================================================
    print("\n[R1a] The accumulated stochastic remnant: one universal a_acc, forms B and S, against the RAR, the constant and Newton")
    fit = {k: S.fit1(MODELS[k], *BOUNDS[k], allidx) for k in BOUNDS}
    n_new, chi_new = S.nll1(SR.m_newton, [], allidx)
    check("reproduces sparc_rotation.py: universal RAR g+ (L1), m/s^2", 10 ** fit["rar"][0], REF["rar_best"], rtol=1e-4)
    check("reproduces sparc_rotation.py: RAR -2 ln L", fit["rar"][1], REF["rar_m2lnL"], atol=0.05)
    check("reproduces sparc_rotation.py: universal constant |gamma1|/2 (L1), m/s^2", 10 ** fit["const"][0], REF["const_best"], rtol=1e-4)
    check("reproduces sparc_rotation.py: constant -2 ln L", fit["const"][1], REF["const_m2lnL"], atol=0.05)
    check("reproduces sparc_rotation.py: Newton -2 ln L", n_new, REF["newton_m2lnL"], atol=0.1)
    for k in ("brown", "simple"):
        check_true(f"the universal fit of form {k} lies inside its search bounds", BOUNDS[k][0] + 0.01 < fit[k][0] < BOUNDS[k][1] - 0.01)
    # analytic slopes against finite differences, and the identities of the two forms
    gtest = np.logspace(-12.5, -8.5, 9)
    ok_sl = True
    for mdl in (m_brown, m_simple):
        h = 1e-6
        fd = (mdl([-10.0], gtest * 10 ** h)[0] - mdl([-10.0], gtest * 10 ** -h)[0]) / (2 * h)
        ok_sl &= bool(np.allclose(fd, mdl([-10.0], gtest)[1], rtol=0, atol=1e-6))
    check_true("analytic log slopes of forms B and S agree with finite differences (1e-6)", ok_sl)
    gS = g_lin("simple", gtest, 1e-10)
    check("form S satisfies (g_obs - g_bar) g_obs = g_bar a_acc (largest relative error)", float(np.max(np.abs((gS - gtest) * gS / (gtest * 1e-10) - 1))),
          0.0, atol=1e-9)
    # synthetic recovery: real g_bar, the error model, an injected a_acc = 1e-10
    rng_s = np.random.default_rng(SEED + 11)
    for k in ("brown", "simple"):
        m_, s_ = MODELS[k]([-10.0], S.g_bar)
        ys = m_ + rng_s.normal(0, 1, N) * np.sqrt(S.so2 + s_ ** 2 * S.sb2)
        ts, _ = S.fit1(MODELS[k], *BOUNDS[k], allidx, arr=(S.g_bar, ys, S.so2, S.sb2))
        check(f"synthetic data: the universal fit of form {k} recovers an injected a_acc = 1e-10 m/s^2 (2%)", 10 ** ts, 1e-10, rtol=0.02)

    rng = np.random.default_rng(SEED + 12)
    bt = {k: [] for k in BOUNDS}
    for _ in range(args.boot):
        bi = S.boot_idx(rng)
        for k in BOUNDS:
            bt[k].append(S.fit1(MODELS[k], *BOUNDS[k], bi)[0])
    bt = {k: np.array(v) for k, v in bt.items()}
    R1a = {}
    for k in ("newton", "rar", "const", "brown", "simple"):
        if k == "newton":
            e = {"k": 0, "m2lnL": n_new, "chi2": chi_new}
            l2 = S.fit2(SR.m_newton, [])
            rob_mad = float(1.4826 * np.median(np.abs((S.y - S.x) - np.median(S.y - S.x))))
            e.update(L2={"sigma_int_dex": l2[1], "m2lnL": l2[2], "BIC": l2[2] + lnN}, robust={"mad_dex": rob_mad})
        else:
            t, nll = fit[k]
            e = {"k": 1, "best": 10 ** t, "log_best": t, "m2lnL": nll, "chi2": S.nll1(MODELS[k], [t], allidx)[1]}
            q = np.percentile(bt[k], [16, 50, 84])
            e["boot_16_50_84"] = [float(10 ** v) for v in q]
            e["boot_sigma_dex"] = float((q[2] - q[0]) / 2)
            l2 = S.fit2(MODELS[k], [t])
            rb = S.robust(MODELS[k], [t])
            e["L2"] = {"best": 10 ** l2[0], "sigma_int_dex": l2[1], "m2lnL": l2[2], "BIC": l2[2] + 2 * lnN}
            e["robust"] = {"best": 10 ** rb[0], "mad_dex": rb[1]}
        e["BIC"] = e["m2lnL"] + e["k"] * lnN
        e["chi2_per_dof"] = e["chi2"] / (N - e["k"])
        R1a[k] = e
    for k in R1a:
        R1a[k]["dBIC_vs_rar"] = R1a[k]["BIC"] - R1a["rar"]["BIC"]
        R1a[k]["L2"]["dBIC_vs_rar"] = R1a[k]["L2"]["BIC"] - R1a["rar"]["L2"]["BIC"]
    # galaxy by galaxy, residuals by acceleration range
    per_gal_univ = {k: np.array([S.nll1(MODELS[k], [fit[k][0]], gi)[0] for gi in S.gal_idx]) for k in BOUNDS}
    R1a["galaxy_counts"] = {f"{a}_beats_{b}": int(np.sum(per_gal_univ[a] < per_gal_univ[b]))
                            for a, b in (("rar", "brown"), ("rar", "simple"), ("simple", "brown"), ("brown", "const"), ("simple", "const"))}
    R1a["galaxy_counts"]["n_galaxies"] = len(S.gal_idx)
    for k in BOUNDS:
        r = S.y - MODELS[k]([fit[k][0]], S.g_bar, S.R)[0]
        R1a[k]["median_resid_dex"] = {"gbar<1e-11": float(np.median(r[S.g_bar < 1e-11])),
                                      "1e-11..1e-10": float(np.median(r[(S.g_bar >= 1e-11) & (S.g_bar < 1e-10)])),
                                      "1e-10..1e-9": float(np.median(r[(S.g_bar >= 1e-10) & (S.g_bar < 1e-9)])),
                                      "gbar>1e-9": float(np.median(r[S.g_bar >= 1e-9]))}
    dg = S.g_obs - S.g_bar
    low_cut = 10 ** fit["rar"][0] / 10
    sl_data, B0, okb = binned_slope(S, dg, low_cut)
    check("reproduces sparc_rotation.py S2d: low-acceleration slope of log(g_obs - g_bar)", sl_data, REF["slope_low"], rtol=1e-4)
    R1a["residual_slope"] = {"data": sl_data, "rar": binned_slope(S, dg, low_cut, lambda g: g_lin("rar", g, 10 ** fit["rar"][0]) - g)[1],
                             "brown": binned_slope(S, dg, low_cut, lambda g: g_lin("brown", g, 10 ** fit["brown"][0]) - g)[1],
                             "simple": binned_slope(S, dg, low_cut, lambda g: g_lin("simple", g, 10 ** fit["simple"][0]) - g)[1],
                             "const": 0.0}
    for k in ("rar", "const", "brown", "simple"):
        e = R1a[k]
        print(f"     {k:7s} best {e['best']:.3e}  [{e['boot_16_50_84'][0]:.3e}, {e['boot_16_50_84'][2]:.3e}]  chi2/dof {e['chi2_per_dof']:.3f}  "
              f"dBIC vs RAR {e['dBIC_vs_rar']:+8.1f} | L2 sigma_int {e['L2']['sigma_int_dex']:.3f}, dBIC {e['L2']['dBIC_vs_rar']:+7.1f} | "
              f"robust MAD {e['robust']['mad_dex']:.3f} | median resid at g_bar > 1e-9: {e['median_resid_dex']['gbar>1e-9']:+.3f}")
    print(f"     galaxy counts: {R1a['galaxy_counts']}")
    print(f"     low-acceleration slope of Delta g: data {sl_data:.3f}; RAR {R1a['residual_slope']['rar']:.3f}, B "
          f"{R1a['residual_slope']['brown']:.3f}, S {R1a['residual_slope']['simple']:.3f}, constant 0")

    # The solar system: both forms are pointwise laws in g_bar and must hold where g_bar is the Sun's field.
    print("\n[R1a'] The solar system: anomalous perihelion precession of each form against planetary ephemerides")
    for n_, eps_ in ((-1, 1e-3), (0, 1e-3)):
        num, ana = precession_numeric(n_, eps_)
        check(f"orbit integration: apsidal advance per orbit for an extra force k r^{n_} (eps = 1e-3) against -pi (n + 2) eps", num, ana, rtol=0.03)
    solar = {}
    for pl, (aAU, P) in PLANETS.items():
        g = GM_SUN / (aAU * AU) ** 2
        row = {"g_sun": g}
        for k, n_ in (("brown", -1), ("simple", 0)):
            eps_ = (g_lin(k, g, 10 ** fit[k][0]) - g) / g
            rate = -math.pi * (n_ + 2) * eps_ / P * (180 / math.pi) * 3600e3      # mas/yr
            row[k] = {"dg_over_g": eps_, "precession_mas_per_yr": rate, "over_bound": abs(rate) / PITJEVA[pl][1]}
        u = math.sqrt(g / 10 ** fit["rar"][0])
        row["rar_log10_dg_over_g"] = float(-u / LOG10)          # exp(-sqrt(g/g+)) to leading order
        solar[pl] = row
        print(f"     {pl:8s} g = {g:.2e}: form B {row['brown']['precession_mas_per_yr']:+.3e} mas/yr ({row['brown']['over_bound']:.1e} x the bound "
              f"{PITJEVA[pl][1]}), form S {row['simple']['precession_mas_per_yr']:+.3e} ({row['simple']['over_bound']:.1e} x); RAR: dg/g ~ 10^{row['rar_log10_dg_over_g']:.0f}")
    R1a["solar_system"] = solar
    o["R1a"] = R1a

    # ===========================================================================================================================
    print("\n[R1b] Parameter-free scales for a_acc, and the look-elsewhere effect")
    cands = {}
    for lab, H in (("67.4", H0_PL), ("73", H0_SH)):
        Hi = math.sqrt(OMEGA_L) * H
        cands[f"c H0 (H0 = {lab})"] = (c * H, lab)
        cands[f"c H0 / 2π (H0 = {lab})"] = (c * H / (2 * math.pi), lab)
        cands[f"c H_inf (H0 = {lab})"] = (c * Hi, lab)
        cands[f"c H_inf / 2π (H0 = {lab})"] = (c * Hi / (2 * math.pi), lab)
    cands["c / t0 (t0 = 13.8 Gyr)"] = (c / T0_TASK, "both")
    check("c H_inf (H0 = 67.4) equals Bridge A's beta -> -infinity value in sparc_rotation.py", cands["c H_inf (H0 = 67.4)"][0], c * SR.H_inf, rtol=1e-12)
    check("c H_inf / 2 pi = 8.6e-11 m/s^2 (paper, Section 11.6)", cands["c H_inf / 2π (H0 = 67.4)"][0], 8.6e-11, rtol=0.01)
    dy674 = np.where(S.fD == 1, math.log10(67.4 / 73.0), 0.0)
    arr674 = S.arrays(dy=dy674)
    R1b = {"candidates": {k: v[0] for k, v in cands.items()}, "forms": {}}
    clog = np.log10([v[0] for v in cands.values()])
    for k in ("brown", "simple"):
        t_nat, n_nat = fit[k]
        t_674, n_674 = S.fit1(MODELS[k], *BOUNDS[k], allidx, arr=arr674)
        t_up = S.fit1(MODELS[k], *BOUNDS[k], allidx, arr=S.arrays(ups=10 ** 0.1))[0]
        t_dn = S.fit1(MODELS[k], *BOUNDS[k], allidx, arr=S.arrays(ups=10 ** -0.1))[0]
        t_l2, t_rb = math.log10(R1a[k]["L2"]["best"]), math.log10(R1a[k]["robust"]["best"])
        s_boot = R1a[k]["boot_sigma_dex"]
        s_ups = abs(t_up - t_dn) / 2
        s_meth = (max(t_nat, t_l2, t_rb) - min(t_nat, t_l2, t_rb)) / 2
        s_tot = math.sqrt(s_boot ** 2 + s_ups ** 2 + s_meth ** 2)
        rows = {}
        for name, (val, h0) in cands.items():
            arr, tb, nb = (arr674, t_674, n_674) if h0 == "67.4" else (None, t_nat, n_nat)
            m2l, chi = S.nll1(MODELS[k], [math.log10(val)], allidx, arr)
            rows[name] = {"value": val, "paired_data": "Hubble-flow distances at 67.4" if h0 == "67.4" else "SPARC distances (73)",
                          "chi2_per_N": chi / N, "dm2lnL_vs_best": m2l - nb, "dBIC_vs_best": m2l - (nb + lnN),
                          "dBIC_vs_rar": m2l - R1a["rar"]["BIC"] if h0 != "67.4" else None,
                          "best_over_candidate": 10 ** tb / val, "dlog_dex": tb - math.log10(val), "n_sigma_tot": (tb - math.log10(val)) / s_tot}
        d_nat = np.abs(t_nat - clog)
        dmin = float(d_nat.min())
        nearest = list(cands)[int(np.argmin(d_nat))]
        wgrid = np.linspace(t_nat - 1, t_nat + 1, 200001)
        dist = np.min(np.abs(wgrid[:, None] - clog[None, :]), axis=1)
        R1b["forms"][k] = {"best_native": 10 ** t_nat, "best_H0_67.4": 10 ** t_674, "best_ups_plus0.1dex": 10 ** t_up, "best_ups_minus0.1dex": 10 ** t_dn,
                           "best_L2": 10 ** t_l2, "best_robust": 10 ** t_rb, "sigma_boot_dex": s_boot, "sigma_ups_dex": s_ups,
                           "sigma_method_dex": s_meth, "sigma_tot_dex": s_tot, "candidates": rows,
                           "look_elsewhere": {"n_candidates": len(cands), "span_dex": float(clog.max() - clog.min()),
                                              "median_spacing_dex": float(np.median(np.diff(np.sort(clog)))),
                                              "nearest": nearest, "nearest_dex": dmin, "nearest_in_sigma_tot": dmin / s_tot,
                                              "p_as_close_in_2dex_window": float(np.mean(dist <= dmin)),
                                              "p_within_1sigma_tot_in_2dex_window": float(np.mean(dist <= s_tot)),
                                              "n_within_2sigma_tot": int(np.sum(d_nat <= 2 * s_tot))}}
        le = R1b["forms"][k]["look_elsewhere"]
        print(f"     form {k}: a_acc = {10 ** t_nat:.3e} (H0 = 67.4 distances: {10 ** t_674:.3e}); sigma boot {s_boot:.3f}, Ups {s_ups:.3f}, "
              f"method {s_meth:.3f}, total {s_tot:.3f} dex; nearest scale {nearest} at {dmin:.3f} dex; chance of being as close: "
              f"{le['p_as_close_in_2dex_window']:.2f}; candidates within 2 sigma: {le['n_within_2sigma_tot']}")
        for name, r in rows.items():
            print(f"        {name:26s} {r['value']:.3e}  best/cand {r['best_over_candidate']:.3f}  dBIC vs own best {r['dBIC_vs_best']:+9.1f}")
    rows_rar = {}
    t_rar674 = S.fit1(SR.m_rar, *BOUNDS["rar"], allidx, arr=arr674)[0]
    for name, (val, h0) in cands.items():
        tb = t_rar674 if h0 == "67.4" else fit["rar"][0]
        rows_rar[name] = {"best_over_candidate": 10 ** tb / val}
    R1b["rar_gdag_over_candidates"] = rows_rar
    R1b["rar_gdag_native"] = 10 ** fit["rar"][0]
    R1b["rar_gdag_H0_67.4"] = 10 ** t_rar674
    tt = np.linspace(-11.6, -8.9, 271)
    R1b["profile"] = {k: [float(S.nll1(MODELS[k], [t], allidx)[0] - fit[k][1]) for t in tt] for k in ("brown", "simple")}
    R1b["profile_t"] = tt.tolist()
    o["R1b"] = R1b

    # ===========================================================================================================================
    print("\n[R1c] a_acc per galaxy (velocity errors per point; distance, inclination, Ups and HI errors as whole-galaxy shifts)")
    g5 = [k for k, gi in enumerate(S.gal_idx) if len(gi) >= 5]
    check("galaxies with at least 5 points (sparc_rotation.py S2c: 132)", len(g5), REF["n_gal5"], rtol=0)
    per = {k: {"t": [], "s_stat": [], "s_sys": [], "chi2": [], "edge": []} for k in ("brown", "simple", "rar")}
    for k5 in g5:
        gi = S.gal_idx[k5]
        n = S.gal_list[k5]
        gg = S.gal[n]
        gb0, ys, sv = S.g_bar[gi], S.y[gi], S.s_V[gi]
        i0, di, d0, dd = math.radians(gg["Inc"]), math.radians(gg["eInc"]), gg["D"], gg["eD"]
        shifts = [({"dy": math.log10(d0 / (d0 + dd))}, {"dy": math.log10(d0 / max(d0 - dd, 0.3 * d0))}),
                  ({"dy": math.log10(math.sin(i0) ** 2 / math.sin(min(i0 + di, math.pi / 2)) ** 2)},
                   {"dy": math.log10(math.sin(i0) ** 2 / math.sin(i0 - di) ** 2)}),
                  ({"star": 1.25}, {"star": 0.75}), ({"gas": 1.10}, {"gas": 0.90})]
        for kind in ("brown", "simple", "rar"):
            t, cmin, ch, edge = grid_fit_chi2(kind, gb0, ys, sv)
            dof = len(gi) - 1
            okc = ch <= cmin + max(1.0, cmin / dof)
            lo, hi = TGRID[np.argmax(okc)], TGRID[len(okc) - 1 - np.argmax(okc[::-1])]
            s_stat = (hi - lo) / 2 if lo > TGRID[0] else (hi - t)
            sh = []
            for kp, km in shifts:
                tp_tm = []
                for kw in (kp, km):
                    gbx = kw.get("gas", 1.0) * S.g_gas[gi] + kw.get("star", 1.0) * S.g_star[gi]
                    tp_tm.append(grid_fit_chi2(kind, gbx, ys + kw.get("dy", 0.0), sv)[0])
                sh.append((tp_tm[0] - tp_tm[1]) / 2)
            per[kind]["t"].append(t)
            per[kind]["s_stat"].append(s_stat)
            per[kind]["s_sys"].append(float(np.sqrt(np.sum(np.square(sh)))))
            per[kind]["chi2"].append(cmin)
            per[kind]["edge"].append(edge)
    for kind in per:
        for kk in per[kind]:
            per[kind][kk] = np.array(per[kind][kk])
        per[kind]["s_tot"] = np.sqrt(per[kind]["s_stat"] ** 2 + per[kind]["s_sys"] ** 2)
    lM5 = np.log10(S.Mbar[g5])
    R1c = {"n_galaxies": len(g5)}
    rng_c = np.random.default_rng(SEED + 13)
    bsel = [rng_c.integers(0, len(g5), len(g5)) for _ in range(args.boot)]
    for kind in ("brown", "simple", "rar"):
        t, st = per[kind]["t"], per[kind]["s_tot"]
        tau, tau68, d0_, mu = scatter_ml(t, st)
        sp = spearman(lM5, t)
        sl = float(np.polyfit(lM5 - 10, t, 1)[0])
        bsl = [float(np.polyfit(lM5[b] - 10, t[b], 1)[0]) for b in bsel]
        R1c[kind] = {"percentiles_16_50_84": [float(10 ** v) for v in np.percentile(t, [16, 50, 84])], "std_dex": float(np.std(t)),
                     "median_sigma_tot_dex": float(np.median(st)), "n_at_grid_edge": int(per[kind]["edge"].sum()),
                     "tau_ml_dex": tau, "tau_68": tau68, "dm2lnL_tau0": d0_, "mean_ml": float(10 ** mu),
                     "chi2_per_dof_tau0": float(np.sum(((t - mu) / st) ** 2) / (len(t) - 1)),
                     "n_within_2sigma_of_mean": int(np.sum(np.abs(t - mu) <= 2 * st)),
                     "spearman_logMbar": list(sp), "slope_vs_logMbar": sl, "slope_boot_16_84": [float(v) for v in np.percentile(bsl, [16, 84])]}
        print(f"     {kind:6s}: median {10 ** np.median(t):.2e}, spread {np.std(t):.3f} dex, median error {np.median(st):.3f} dex, "
              f"intrinsic scatter {tau:.3f} dex [{tau68[0]:.3f}, {tau68[1]:.3f}] (Delta -2lnL of tau = 0: {d0_:.1f}); vs log Mbar: Spearman "
              f"{sp[0]:+.2f} (p = {sp[1]:.1e}), slope {sl:+.3f}")
    R1c["shape_counts"] = {"rar_beats_brown": int(np.sum(per["rar"]["chi2"] < per["brown"]["chi2"])),
                           "rar_beats_simple": int(np.sum(per["rar"]["chi2"] < per["simple"]["chi2"])),
                           "simple_beats_brown": int(np.sum(per["simple"]["chi2"] < per["brown"]["chi2"])),
                           "chi2_sum": {k: float(per[k]["chi2"].sum()) for k in per}, "n_points": int(sum(len(S.gal_idx[k]) for k in g5))}
    print(f"     shape within galaxies (one free scale each): {R1c['shape_counts']}")
    # synthetic per-galaxy recovery (velocity-error noise only), and an exact recovery without noise
    rng_g = np.random.default_rng(SEED + 14)
    rec, rec0 = [], []
    for k5 in g5:
        gi = S.gal_idx[k5]
        ytrue = np.log10(g_lin("brown", S.g_bar[gi], 1e-10))
        rec.append(grid_fit_chi2("brown", S.g_bar[gi], ytrue + rng_g.normal(0, 1, len(gi)) * S.s_V[gi], S.s_V[gi])[0])
        rec0.append(grid_fit_chi2("brown", S.g_bar[gi], ytrue, S.s_V[gi])[0])
    check("synthetic galaxies: median per-galaxy a_acc (form B) recovers an injected 1e-10 m/s^2 (5%)", 10 ** np.median(rec), 1e-10, rtol=0.05)
    check("noise-free synthetic galaxies: the grid fitter returns the injected log a_acc exactly (largest error, dex)",
          float(np.max(np.abs(np.array(rec0) + 10))), 0.0, atol=2e-3)
    o["R1c"] = R1c

    # ===========================================================================================================================
    print("\n[R2] History: per-galaxy quantities against history proxies (rank correlations, bootstrap, Holm, mock-universe nulls)")
    a_b = 10 ** fit["brown"][0]
    gd5 = [S.gal_data(k) for k in g5]

    def resid_mean(yv, t_univ):
        out = []
        for gd in gd5:
            m, s = m_brown([t_univ], gd["gb"])
            var = gd["so2"] + s * s * gd["sb2"]
            out.append(float(np.sum((yv[gd["gi"]] - m) / var) / np.sum(1 / var)))
        return np.array(out)

    Q = {"log a_acc (B, per galaxy)": per["brown"]["t"], "mean residual from universal B [dex]": resid_mean(S.y, fit["brown"][0]),
         "log g+ (RAR, per galaxy)": per["rar"]["t"]}
    Pp = {"Hubble type T": S.T[g5], "gas fraction": S.fgas[g5], "log SB_eff": np.log10(S.SBeff[g5]), "log R_disk": np.log10(S.Rdisk[g5]),
          "log N_orb": np.log10(S.Norb[g5])}
    pred_sign = {"Hubble type T": -1, "gas fraction": -1, "log SB_eff": +1, "log R_disk": -1, "log N_orb": +1}
    pairs = [(qk, pk) for qk in Q for pk in Pp]

    def corr_set(Qd):
        raw = [spearman(Pp[pk], Qd[qk]) for qk, pk in pairs]
        par = [partial_spearman(Pp[pk], Qd[qk], lM5) for qk, pk in pairs]
        return raw, par

    raw, par = corr_set(Q)
    p_all = [r[1] for r in raw] + [r[1] for r in par]
    p_holm = holm(p_all)
    check("Holm correction reproduces a hand-worked example ([0.01, 0.04, 0.03] -> [0.03, 0.06, 0.06])",
          float(np.max(np.abs(holm([0.01, 0.04, 0.03]) - np.array([0.03, 0.06, 0.06])))), 0.0, atol=1e-12)
    check("partial Spearman of a variable with itself, controlling for mass, is 1", partial_spearman(lM5 + S.T[g5], lM5 + S.T[g5], lM5)[0], 1.0, rtol=1e-12)
    rng_r = np.random.default_rng(SEED + 15)
    bsr = {i: [] for i in range(len(pairs))}
    bsp = {i: [] for i in range(len(pairs))}
    for b in bsel:
        for i, (qk, pk) in enumerate(pairs):
            bsr[i].append(stats.spearmanr(Pp[pk][b], Q[qk][b]).statistic)
            bsp[i].append(partial_spearman(Pp[pk][b], Q[qk][b], lM5[b])[0])
    # Mock universes: the per-galaxy analysis applied to data drawn from a universal law with the SPARC error model. Extra per-point
    # scatter sigma_x (non-circular motions) is calibrated so that the median per-galaxy reduced chi^2 of the free RAR fit matches the data.
    chi_red = per["rar"]["chi2"] / (np.array([len(S.gal_idx[k]) for k in g5]) - 1)
    m_d = float(np.median(chi_red))
    sV5 = [S.s_V[S.gal_idx[k]] for k in g5]

    def red_of(sx):
        return float(np.median([np.mean(1 + sx * sx / (s * s)) for s in sV5]))

    sig_x = optimize.brentq(lambda sx: red_of(sx) - m_d, 0.0, 1.0) if m_d > 1 else 0.0
    print(f"     median per-galaxy reduced chi^2 (free RAR, velocity errors): {m_d:.2f}; mock extra point scatter sigma_x = {sig_x:.3f} dex")
    rng_m = np.random.default_rng(SEED + 16)
    sinI = np.sin(np.radians(S.inc))
    null = {}
    mock_spread = {}
    for truth in ("rar", "brown"):
        th = 10 ** fit[truth][0]
        rr, pp, spr, taum = [], [], [], []
        for _ in range(args.mock):
            ng = len(S.gal_idx)
            dD = np.maximum(rng_m.normal(0, 1, ng) * S.eD_rel, -0.7)
            di = rng_m.normal(0, 1, ng) * S.einc_g
            fs = 10 ** rng_m.normal(0, 0.1, ng)
            fg = 1 + 0.1 * rng_m.normal(0, 1, ng)
            p_ = S.pt_gal
            gbt = np.maximum(S.g_gas * fg[p_] + S.g_star * fs[p_], 1e-13)
            itrue = np.radians(np.clip(S.inc + di[p_], 5.0, 90.0))
            ym = (np.log10(g_lin(truth, gbt, th) * (1 + dD[p_]) * np.sin(itrue) ** 2 / sinI ** 2)
                  + rng_m.normal(0, 1, N) * np.sqrt(S.s_V ** 2 + sig_x ** 2))
            tu = S.fit1(m_brown, *BOUNDS["brown"], allidx, arr=(S.g_bar, ym, S.so2, S.sb2))[0]
            Qm = {"log a_acc (B, per galaxy)": np.array([grid_fit_chi2("brown", gd["gb"], ym[gd["gi"]], gd["sV"])[0] for gd in gd5]),
                  "mean residual from universal B [dex]": resid_mean(ym, tu),
                  "log g+ (RAR, per galaxy)": np.array([grid_fit_chi2("rar", gd["gb"], ym[gd["gi"]], gd["sV"])[0] for gd in gd5])}
            r_, p2_ = corr_set(Qm)
            rr.append([v[0] for v in r_])
            pp.append([v[0] for v in p2_])
            spr.append([float(np.std(Qm[qk_])) for qk_ in Q])
            taum.append([tau_fast(Qm["log a_acc (B, per galaxy)"], per["brown"]["s_tot"]), tau_fast(Qm["log g+ (RAR, per galaxy)"], per["rar"]["s_tot"])])
        null[truth] = (np.array(rr), np.array(pp))
        mock_spread[truth] = {qk_: float(v) for qk_, v in zip(Q, np.mean(spr, axis=0))}
        taum = np.array(taum)
        mock_spread[truth]["tau_brown_16_50_84"] = [float(v) for v in np.percentile(taum[:, 0], [16, 50, 84])]
        mock_spread[truth]["tau_rar_16_50_84"] = [float(v) for v in np.percentile(taum[:, 1], [16, 50, 84])]
    check("the vectorised intrinsic-scatter estimator agrees with the profile estimator on the data (form B a_acc, dex)",
          tau_fast(per["brown"]["t"], per["brown"]["s_tot"]), R1c["brown"]["tau_ml_dex"], atol=0.0026)
    R2 = {"n_galaxies": len(g5), "sigma_x_mock_dex": sig_x, "median_red_chi2_data": m_d, "predicted_sign": pred_sign, "tests": [],
          "spread_data_dex": {qk_: float(np.std(v)) for qk_, v in Q.items()}, "spread_mock_dex": mock_spread}
    # Shift test: the mock-null mean (universal RAR) is the correlation that shape mismatch and shared variables produce; the data's own
    # galaxy bootstrap gives the sampling spread (the mocks lack the extra galaxy-to-galaxy scatter of the data, so their bands are too
    # narrow to serve as the error). z = (rho - null mean) / bootstrap sd, two-sided, Holm over all 30.
    p_shift = []
    for i in range(len(pairs)):
        p_shift.append(2 * stats.norm.sf(abs(raw[i][0] - np.mean(null["rar"][0][:, i])) / np.std(bsr[i])))
    for i in range(len(pairs)):
        p_shift.append(2 * stats.norm.sf(abs(par[i][0] - np.mean(null["rar"][1][:, i])) / np.std(bsp[i])))
    p_shift_holm = holm(p_shift)
    for i, (qk, pk) in enumerate(pairs):
        e = {"quantity": qk, "proxy": pk, "rho": raw[i][0], "p": raw[i][1], "p_holm": float(p_holm[i]),
             "rho_boot_2.5_97.5": [float(v) for v in np.percentile(bsr[i], [2.5, 97.5])],
             "partial_rho": par[i][0], "partial_p": par[i][1], "partial_p_holm": float(p_holm[len(pairs) + i]),
             "partial_boot_2.5_97.5": [float(v) for v in np.percentile(bsp[i], [2.5, 97.5])]}
        for truth in ("rar", "brown"):
            rr, pp = null[truth]
            e[f"null_{truth}_rho_mean"] = float(np.mean(rr[:, i]))
            e[f"null_{truth}_rho_2.5_97.5"] = [float(v) for v in np.percentile(rr[:, i], [2.5, 97.5])]
            e[f"null_{truth}_partial_mean"] = float(np.mean(pp[:, i]))
            e[f"null_{truth}_partial_2.5_97.5"] = [float(v) for v in np.percentile(pp[:, i], [2.5, 97.5])]
        e["outside_null_rar"] = not (e["null_rar_rho_2.5_97.5"][0] <= e["rho"] <= e["null_rar_rho_2.5_97.5"][1])
        e["partial_outside_null_rar"] = not (e["null_rar_partial_2.5_97.5"][0] <= e["partial_rho"] <= e["null_rar_partial_2.5_97.5"][1])
        e["sign_as_predicted"] = bool(np.sign(e["rho"]) == pred_sign[pk]) if qk.startswith("log a_acc") else None
        e["shift_vs_null_rar"] = e["rho"] - e["null_rar_rho_mean"]
        e["shift_p_holm"] = float(p_shift_holm[i])
        e["partial_shift_vs_null_rar"] = e["partial_rho"] - e["null_rar_partial_mean"]
        e["partial_shift_p_holm"] = float(p_shift_holm[len(pairs) + i])
        R2["tests"].append(e)
        print(f"     {qk[:28]:28s} vs {pk:14s} rho {e['rho']:+.2f} [{e['rho_boot_2.5_97.5'][0]:+.2f}, {e['rho_boot_2.5_97.5'][1]:+.2f}] "
              f"p_Holm {e['p_holm']:.2g} | null(RAR) [{e['null_rar_rho_2.5_97.5'][0]:+.2f}, {e['null_rar_rho_2.5_97.5'][1]:+.2f}] | "
              f"partial {e['partial_rho']:+.2f} p_Holm {e['partial_p_holm']:.2g} null [{e['null_rar_partial_2.5_97.5'][0]:+.2f}, "
              f"{e['null_rar_partial_2.5_97.5'][1]:+.2f}] | shift p_Holm {e['shift_p_holm']:.2g}, partial {e['partial_shift_p_holm']:.2g}")
    print(f"     spread of the per-galaxy quantities, data: {R2['spread_data_dex']}; mocks (universal RAR): {mock_spread['rar']}")
    lN = Pp["log N_orb"]
    tb_ = per["brown"]["t"]
    sl_N = float(np.polyfit(lN, tb_, 1)[0])
    R2["slope_log_a_vs_log_Norb"] = {"slope": sl_N, "boot_2.5_97.5": [float(v) for v in np.percentile([np.polyfit(lN[b], tb_[b], 1)[0] for b in bsel], [2.5, 97.5])],
                                     "per_orbit_random_walk_predicts": 1.0, "universal_predicts": 0.0}
    R2["Norb_percentiles_16_50_84"] = [float(v) for v in np.percentile(S.Norb[g5], [16, 50, 84])]
    print(f"     log a_acc against log N_orb: slope {sl_N:+.3f} {R2['slope_log_a_vs_log_Norb']['boot_2.5_97.5']} (per-orbit random walk: +1; universal: 0)")
    o["R2"] = R2

    # ===========================================================================================================================
    print("\n[R3] The contained remnant: baryons + a cold, collisionless halo per galaxy")
    # checks on the halo profiles and priors
    check("NFW enclosed mass at r200 equals M200", float(halo_menc("nfw", np.cbrt(3 * 1e12 / (800 * math.pi * RHO_C)), 12.0, 1.0)), 1e12, rtol=1e-12)
    rq = integrate.quad(lambda r: 4 * math.pi * r * r * 1e7 / ((1 + r / 3.0) * (1 + (r / 3.0) ** 2)), 0, 7.0, epsabs=0, epsrel=1e-12)[0]
    check("Burkert enclosed mass against direct integration of its density (rho0 = 1e7 Msun/kpc^3, r0 = 3 kpc, r = 7 kpc)",
          float(halo_menc("burkert", 7.0, 7.0, math.log10(3.0))), rq, rtol=1e-9)
    check("Dutton-Maccio c200 at M200 = 1e12 h^-1 Msun is 10^0.905", 10 ** (DM14["a"] + DM14["b"] * (math.log10(1e12 / H_LITTLE) + math.log10(H_LITTLE) - 12)),
          10 ** 0.905, rtol=1e-12)
    check("Moster et al. SHMR: m/M = N at M = M1", 10 ** (lmstar_mnw13(MNW13["logM1"]) - MNW13["logM1"]), MNW13["N"], rtol=1e-12)
    # synthetic halo recovery on a real galaxy's baryons
    ksyn = max(range(len(gd5)), key=lambda i: len(gd5[i]["gb"]))
    gs = dict(gd5[ksyn])
    rng_h = np.random.default_rng(SEED + 17)
    gtrue = gs["gb"] + g_halo("nfw", gs["R"], 11.5, 1.0)
    gs["y"] = np.log10(gtrue) + rng_h.normal(0, 1, len(gtrue)) * 0.02
    gs["so2"] = np.full(len(gtrue), 0.02 ** 2)
    gs["sb2"] = np.zeros(len(gtrue))
    p_syn, _, _ = fit_halo("nfw_cm", gs)
    check_true(f"synthetic galaxy ({S.gal_list[g5[ksyn]]}'s baryons + NFW 10^11.5 Msun, c = 10): fitted log M200 = {p_syn[0]:.2f} within 0.15 dex",
               abs(p_syn[0] - 11.5) < 0.15)
    hk_list = ("nfw_cm", "nfw_shmr", "burkert")
    halo = {hk: [fit_halo(hk, gd) for gd in gd5] for hk in hk_list}
    n5 = np.array([len(gd["gb"]) for gd in gd5])
    N5 = int(n5.sum())
    m2 = {}
    for k in ("rar", "brown", "simple", "const"):
        m2[k] = np.array([S.nll1(MODELS[k], [fit[k][0]], gd["gi"])[0] for gd in gd5])
    for k in ("rar", "brown"):
        m2[k + "_free"] = np.array([grid_fit_l1(k, gd)[1] for gd in gd5])
    for hk in hk_list:
        m2[hk] = np.array([h[2] for h in halo[hk]])
    kpg = {"rar": 0, "brown": 0, "simple": 0, "const": 0, "rar_free": 1, "brown_free": 1, "nfw_cm": 2, "nfw_shmr": 2, "burkert": 2}
    kglob = {"rar": 1, "brown": 1, "simple": 1, "const": 1, "rar_free": len(gd5), "brown_free": len(gd5), "nfw_cm": 2 * len(gd5),
             "nfw_shmr": 2 * len(gd5), "burkert": 2 * len(gd5)}
    bic_i = {k: m2[k] + kpg[k] * np.log(n5) for k in m2}
    R3 = {"n_galaxies": len(gd5), "n_points": N5, "models": {}}
    for k in m2:
        tot = float(m2[k].sum() + kglob[k] * math.log(N5))
        R3["models"][k] = {"k_per_galaxy": kpg[k], "k_total": kglob[k], "m2lnL": float(m2[k].sum()), "BIC_total": tot,
                           "n_galaxies_better_than_rar_univ": int(np.sum(bic_i[k] < bic_i["rar"])),
                           "n_galaxies_better_than_brown_univ": int(np.sum(bic_i[k] < bic_i["brown"])),
                           "median_dBIC_i_vs_rar_univ": float(np.median(bic_i[k] - bic_i["rar"]))}
    for k in m2:
        R3["models"][k]["dBIC_total_vs_rar_univ"] = R3["models"][k]["BIC_total"] - R3["models"]["rar"]["BIC_total"]
        print(f"     {k:9s} k = {kglob[k]:4d}  -2lnL {m2[k].sum():10.1f}  dBIC(total) vs RAR {R3['models'][k]['dBIC_total_vs_rar_univ']:+9.1f}  "
              f"galaxies better than RAR (per-galaxy BIC): {R3['models'][k]['n_galaxies_better_than_rar_univ']:3d}/{len(gd5)}, "
              f"than form B: {R3['models'][k]['n_galaxies_better_than_brown_univ']:3d}")
    for hk in hk_list:
        P_ = np.array([h[0] for h in halo[hk]])
        base = "burkert" if hk == "burkert" else "nfw"
        (lo1, hi1), (lo2, hi2) = HBOUNDS[base]
        at_b = int(np.sum((np.abs(P_[:, 0] - lo1) < 1e-3) | (np.abs(P_[:, 0] - hi1) < 1e-3) | (np.abs(P_[:, 1] - lo2) < 1e-3) | (np.abs(P_[:, 1] - hi2) < 1e-3)))
        R3["models"][hk]["param_percentiles_16_50_84"] = [[float(v) for v in np.percentile(P_[:, j], [16, 50, 84])] for j in (0, 1)]
        R3["models"][hk]["n_at_bounds"] = at_b
        if hk.startswith("nfw"):
            R3["models"][hk]["median_log_M200_over_Mbar"] = float(np.median(P_[:, 0] - lM5))
    # per-galaxy listing for the JSON
    R3["per_galaxy"] = [{"galaxy": S.gal_list[g5[i]], "n": int(n5[i]), **{f"m2lnL_{k}": float(m2[k][i]) for k in m2},
                         **{f"params_{hk}": halo[hk][i][0] for hk in hk_list}} for i in range(len(gd5))]
    o["R3"] = R3

    # ===========================================================================================================================
    print("\n[R4] The whole: baryons + halo + one universal stochastic term, profile likelihood over its amplitude")
    TA = np.round(np.arange(-16.0, -9.4999, 0.1), 3)   # sqrt(g_bar A) is 1% of g_bar = 1e-12 at A = 1e-16
    R4 = {"grid_log_A": TA.tolist(), "n_points": N5, "ln_N": math.log(N5), "fits": {}}
    lnN5 = math.log(N5)
    PRO = {}
    for hk in hk_list:
        for sk in ("const", "sqrt"):
            P = np.empty((len(gd5), len(TA) + 1))
            Lm = np.empty_like(P)
            for i, gd in enumerate(gd5):
                P[i, 0], Lm[i, 0] = halo[hk][i][1], halo[hk][i][2]
                for j, t in enumerate(TA):
                    _, P[i, j + 1], Lm[i, j + 1] = fit_halo(hk, gd, sk, 10 ** t)
            PRO[(hk, sk)] = (P, Lm)

    def summary(P):
        T0_, T_ = float(P[:, 0].sum()), P[:, 1:].sum(axis=0)
        k = int(np.argmin(T_))
        if T_[k] < T0_:
            if 0 < k < len(TA) - 1:
                d, Tb = parabola(T_, k, 0.1)
                tb = TA[k] + d
            else:
                tb, Tb = TA[k], T_[k]
            zero = False
        else:
            tb, Tb, zero = None, T0_, True
        thr = min(Tb, T0_) + 2.71
        t95 = None
        for j in range(0 if zero else k, len(TA)):
            if T_[j] >= thr:
                t95 = float(TA[0]) if j == 0 else float(TA[j - 1] + (thr - T_[j - 1]) / (T_[j] - T_[j - 1]) * 0.1)
                break
        tlo = None
        if not zero and T0_ - Tb > 2.71:
            for j in range(k, -1, -1):
                if T_[j] >= Tb + 2.71:
                    tlo = float(TA[j] + (Tb + 2.71 - T_[j]) / (T_[j + 1] - T_[j]) * 0.1)
                    break
        return {"best_at_zero": zero, "log_A_best": tb, "dm2lnL_best_minus_zero": float(Tb - T0_), "dBIC_add_term": float(Tb - T0_ + lnN5),
                "log_A_95_upper": t95, "log_A_95_lower": tlo}, T_ - min(Tb, T0_)

    a_r1 = {"sqrt": 10 ** fit["brown"][0], "const": 10 ** fit["const"][0]}
    rng_4 = np.random.default_rng(SEED + 18)
    picks = [rng_4.integers(0, len(gd5), len(gd5)) for _ in range(args.boot)]
    outer_pt = [gd["gi"][int(np.argmax(gd["R"]))] for gd in gd5]
    gbo, gob = S.g_bar[outer_pt], S.g_obs[outer_pt]
    dark = gob - gbo
    okd = dark > 0
    for (hk, sk), (P, Lm) in PRO.items():
        sm, curve = summary(P)
        bs = [summary(P[b])[0] for b in picks]
        # coded for percentiles: no crossing inside the grid -> top of the grid; best at A = 0 -> one step below the grid
        t95b = np.array([b_["log_A_95_upper"] if b_["log_A_95_upper"] is not None else TA[-1] for b_ in bs])
        frac_zero = float(np.mean([b_["best_at_zero"] for b_ in bs]))
        sm["boot_frac_no_upper_bound_in_grid"] = float(np.mean([b_["log_A_95_upper"] is None for b_ in bs]))
        tbest_b = np.array([b_["log_A_best"] if b_["log_A_best"] is not None else TA[0] - 0.1 for b_ in bs])
        sm["boot_frac_best_at_zero"] = frac_zero
        sm["boot_log_A_best_16_50_84"] = [float(v) for v in np.percentile(tbest_b, [16, 50, 84])]
        sm["boot_log_A_95_16_50_84"] = [float(v) for v in np.percentile(t95b, [16, 50, 84])]
        sm["boot_log_A_95_95th"] = float(np.percentile(t95b, 95))
        sm["dm2lnL_curve"] = [float(v) for v in curve]
        sm["dm2lnL_lnL_only_best_minus_zero"] = float(Lm[:, 1:].sum(axis=0)[int(np.argmin(P[:, 1:].sum(axis=0)))] - Lm[:, 0].sum())
        ref = a_r1[sk]
        for lab, tv in (("A95", sm["log_A_95_upper"]), ("A95_boot84", sm["boot_log_A_95_16_50_84"][2])):
            if tv is not None and np.isfinite(tv):
                A = 10 ** tv
                sfrac = (A if sk == "const" else np.sqrt(gbo * A)) / dark
                sm[f"{lab}_over_R1_value"] = A / ref
                sm[f"{lab}_frac_of_dark_accel_outer_median"] = float(np.median(sfrac[okd]))
                sm[f"{lab}_frac_of_dark_accel_outer_84"] = float(np.percentile(sfrac[okd], 84))
        if not sm["best_at_zero"]:
            A = 10 ** sm["log_A_best"]
            sfrac = (A if sk == "const" else np.sqrt(gbo * A)) / dark
            sm["best_over_R1_value"] = A / ref
            sm["best_frac_of_dark_accel_outer_median"] = float(np.median(sfrac[okd]))
        R4["fits"][f"{hk}+{sk}"] = sm
        t95s = "none in grid" if sm["log_A_95_upper"] is None else f"{10 ** sm['log_A_95_upper']:.2e}"
        print(f"     {hk:8s} + {sk:5s}: best {'A = 0' if sm['best_at_zero'] else f'A = {10 ** sm['log_A_best']:.2e}'}, "
              f"Delta(-2lnL) {sm['dm2lnL_best_minus_zero']:+.1f}, dBIC(add) {sm['dBIC_add_term']:+.1f}; A95 {t95s} "
              f"(bootstrap 84%: 10^{sm['boot_log_A_95_16_50_84'][2]:.2f}); best at zero in {frac_zero:.0%} of resamples")
    tot0 = sum(abs(fit_halo(hk, gd, "sqrt", 1e-30)[1] - halo[hk][i][1]) for hk in hk_list for i, gd in enumerate(gd5))
    check("the joint fitter with a vanishing term (A = 1e-30) reproduces the halo-only fits (summed |Delta -2 ln L|, all halo models)",
          tot0, 0.0, atol=0.5)
    o["R4"] = R4

    # ===========================================================================================================================
    print("\n[R5] Cosmic time: a_acc(z) laws against published high-redshift kinematics")
    tq = integrate.quad(lambda z: 1 / ((1 + z) * H0_PL * E_of_z(z)), 1.0, np.inf, epsabs=0, epsrel=1e-12)[0]
    check("flat-LCDM age at z = 1: closed form against numerical integration", t_of_z(1.0), tq, rtol=1e-8)
    gd0 = 10 ** fit["rar"][0]
    zs = [0.9, 1.0, 2.0, 2.3]
    R5 = {"t0_LCDM_Gyr": t_of_z(0) / GYR, "laws": {}, "zs": zs}
    for lw, f in LAWS.items():
        e = {}
        for z in zs:
            r = f(z)
            e[str(z)] = {"ratio": r, "db_deep": -math.log10(r), "db_x3": db_regime(r, 3.0, gd0), "db_x10": db_regime(r, 10.0, gd0)}
        R5["laws"][lw] = e
        print(f"     {lw:17s} " + "  ".join(f"z={z}: a(z)/a(0) {e[str(z)]['ratio']:.2f}, db deep {e[str(z)]['db_deep']:+.2f}, x=3 {e[str(z)]['db_x3']:+.2f}" for z in zs))
    imp = {}
    for z, db in zip(UBLER17["z"], UBLER17["db"]):
        r3 = 10 ** optimize.brentq(lambda lr: db_regime(10 ** lr, 3.0, gd0) - db, -3, 3)
        imp[str(z)] = {"deep": 10 ** -db, "x3": r3}
    R5["ubler_implied_ratio"] = imp
    R5["musedark_ratio_vs_local"] = MUSEDARK["a0_z1"] / MUSEDARK["a0_local"]
    R5["musedark_ratio_vs_local_err"] = R5["musedark_ratio_vs_local"] * math.hypot(MUSEDARK["a0_z1_hi"] / MUSEDARK["a0_z1"], MUSEDARK["a0_local_err"] / MUSEDARK["a0_local"])
    R5["musedark_ratio_own_fit"] = (MUSEDARK["a0_0_fit"] + MUSEDARK["a1"]) / MUSEDARK["a0_0_fit"]
    R5["inputs"] = {"Ubler2017": UBLER17, "MUSE-DARK_III": MUSEDARK, "RC100": RC100}
    print(f"     Ubler et al. 2017 implied a(z)/a(0): {imp}; MUSE-DARK III at z~1: {R5['musedark_ratio_vs_local']:.2f} "
          f"(own linear fit {R5['musedark_ratio_own_fit']:.2f}); Milgrom 2017: ~4 a0 at z ~ 2 all but excluded")
    o["R5"] = R5
    o["constants"] = {"H0_planck": 67.4, "H0_sparc": 73.0, "Omega_L": OMEGA_L, "Omega_m": OMEGA_M, "t0_Gyr_task": 13.8, "rho_crit_Msun_kpc3": RHO_C,
                      "DM14": DM14, "MNW13": MNW13, "ups_disk": UPS_D, "ups_bul": UPS_B}
    o["checks"] = check_log
    RESULTS.mkdir(parents=True, exist_ok=True)
    (RESULTS / "remnant_history.json").write_text(json.dumps(SR.sig(o), indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    (RESULTS / "remnant_history.md").write_text(markdown(SR.sig(o)), encoding="utf-8")
    if not args.no_figures:
        figures(S, SR.sig(o), fit, per, Q, Pp, g5, null, PRO, TA, a_r1, B0, okb)
    print(f"\n{sum(results)} of {len(results)} checks passed")
    raise SystemExit(0 if all(results) else 1)


# ---------------------------------------------------------------------------------------------------------------------------------

def e2(v, d=2):
    return f"{v:.{d}e}"


def p10(t, d=2):
    """10^t written as 1.23e-11 (t may be None)."""
    return "none in grid" if t is None else e2(10 ** t, d)


def markdown(o):
    a, b, cc, h2, h3, h4, z5 = o["R1a"], o["R1b"], o["R1c"], o["R2"], o["R3"], o["R4"], o["R5"]
    n_ok = sum(1 for k in o["checks"] if k["ok"])
    n_all = len(o["checks"])
    B, Sf = b["forms"]["brown"], b["forms"]["simple"]
    leB, leS = B["look_elsewhere"], Sf["look_elsewhere"]
    M = h3["models"]
    F = h4["fits"]
    L = []
    w = L.append
    w("# Remnants with a history: the stochastic and the contained remnant against SPARC and high-redshift kinematics")
    w("")
    w("Workstream of *GUID v6: Our theory as simulated*. Written by `docs/simulation/remnant_history.py` from one run (seed "
      f"{o['seed']}, {o['n_boot']} galaxy-bootstrap resamples, {o['n_mock']} mock universes per null model); every number is also in "
      "`remnant_history.json`. Figures: `docs/simulation/figures/remnant_forms.pdf`, `remnant_scales.pdf`, `remnant_history.pdf`, "
      f"`remnant_halos.pdf`, `remnant_redshift.pdf`. Checks: **{n_ok} of {n_all} passed** (pipeline reproduction and internal "
      "consistency; every model comparison below is a result, not a check). The data, cuts, error model and likelihoods are those of "
      "`sparc_rotation.py`, imported or copied from it, and its universal fits are reproduced to 1e-4.")
    w("")
    w("The question: `sparc_rotation.py` rejected a static, constant extra acceleration |γ1|/2 (the residual slope d log(g_obs - g_bar) / "
      "d log g_bar is 0.44, a constant gives 0). The theory proposes a long cosmic evolution in which remnants accumulate. What does it "
      "allow once history is included, and does a cohesive whole emerge?")
    w("")
    w("## Verdict")
    w("")
    w(f"- **R1, accumulated stochastic remnant.** As a hypothesis, a random walk of the field's kicks gives g_obs = g_bar + √(g_bar a_acc) "
      f"(form B) or, if the excess is sourced by the total field, g_obs = g_bar/2 + √(g_bar²/4 + g_bar a_acc) (form S). Form S fits SPARC "
      f"as well as the RAR (ΔBIC {a['simple']['dBIC_vs_rar']:+.1f} with the stated errors, {a['simple']['L2']['dBIC_vs_rar']:+.1f} with a "
      f"fitted floor), with a_acc = {e2(a['simple']['best'])} m/s² (bootstrap 16-84%: {e2(a['simple']['boot_16_50_84'][0])} to "
      f"{e2(a['simple']['boot_16_50_84'][2])}). Form B is worse (ΔBIC {a['brown']['dBIC_vs_rar']:+.0f}; a_acc = {e2(a['brown']['best'])}) "
      f"because it overshoots at high acceleration (median residual {a['brown']['median_resid_dex']['gbar>1e-9']:+.3f} dex at g_bar > 1e-9). "
      f"Both beat the constant (by ΔBIC {a['const']['BIC'] - a['brown']['BIC']:.0f} and {a['const']['BIC'] - a['simple']['BIC']:.0f}). "
      "Both forms are MOND's phenomenology under a new name: S is Milgrom's \"simple\" "
      "interpolating function. And the sqrt form was proposed after the slope 0.44 was measured, so matching it is not a prediction.")
    w(f"- **R1, the solar system excludes both forms as written.** Applied pointwise in the Sun's field, form B adds a perihelion "
      f"precession of {a['solar_system']['Mars']['brown']['precession_mas_per_yr']:+.1e} mas/yr at Mars, "
      f"{a['solar_system']['Mars']['brown']['over_bound']:.0e} times the ephemeris bound; form S adds "
      f"{a['solar_system']['Saturn']['simple']['precession_mas_per_yr']:+.0f} mas/yr at Saturn, "
      f"{a['solar_system']['Saturn']['simple']['over_bound']:.0e} times its bound (Pitjeva and Pitjev 2013). A version that survives "
      "needs an extra rule that switches the term off at high acceleration (the RAR's exponential does), which the accumulation picture "
      "does not supply.")
    w(f"- **R1, natural scales.** Of nine candidate scales, the nearest to form S's a_acc is {leS['nearest']} ({leS['nearest_dex']:.3f} dex "
      f"away; a_acc/cH0/2π = {Sf['candidates']['c H0 / 2π (H0 = 67.4)']['best_over_candidate']:.2f} with distances rescaled to H0 = 67.4 "
      f"and {Sf['candidates']['c H0 / 2π (H0 = 73)']['best_over_candidate']:.2f} at 73). This is Milgrom's known coincidence a0 ≈ cH0/2π, "
      f"not a test: the total uncertainty on a_acc is {Sf['sigma_tot_dex']:.2f} dex (mostly the stellar M/L), "
      f"{leS['n_within_2sigma_tot']} of the 9 candidates lie within 2σ of it, and a scale drawn at random within ±1 dex would land as "
      f"close to one of them with probability {leS['p_as_close_in_2dex_window']:.2f}. The scales without 2π (cH0, cH_inf, c/t0, "
      f"5.4e-10 to 7.1e-10) are excluded by ΔBIC ≥ {min(f_['candidates'][n_]['dBIC_vs_best'] for f_ in (B, Sf) for n_ in f_['candidates'] if '2π' not in n_):.0f}, "
      "as Bridge A was.")
    tB = h2["tests"][:5]
    nB_out = sum(1 for t in h2["tests"] if t["outside_null_rar"])
    nP_out = sum(1 for t in h2["tests"] if t["partial_outside_null_rar"])
    nB_sig = sum(1 for t in h2["tests"] if t["p_holm"] < 0.05)
    nP_sig = sum(1 for t in h2["tests"] if t["partial_p_holm"] < 0.05)
    nS_sig = sum(1 for t in h2["tests"] if t["shift_p_holm"] < 0.05)
    nSP_sig = sum(1 for t in h2["tests"] if t["partial_shift_p_holm"] < 0.05)
    sig_list = [f"{t['quantity'].split(' (')[0]} vs {t['proxy']}" for t in h2["tests"] if t["shift_p_holm"] < 0.05 or t["partial_shift_p_holm"] < 0.05]
    tau_all = all(cc[k]["dm2lnL_tau0"] > 4 for k in ("brown", "simple", "rar"))
    mt = h2["spread_mock_dex"]["rar"]
    art = cc["brown"]["tau_ml_dex"] <= mt["tau_brown_16_50_84"][2] and cc["rar"]["tau_ml_dex"] <= mt["tau_rar_16_50_84"][2]
    w(f"- **R1c and R2, history.** Per galaxy, a_acc (form B) has a spread of {cc['brown']['std_dex']:.2f} dex and, against the per-galaxy "
      f"error estimates, an intrinsic scatter of {cc['brown']['tau_ml_dex']:.2f} dex (form S {cc['simple']['tau_ml_dex']:.2f}; the RAR's g† "
      f"{cc['rar']['tau_ml_dex']:.2f}, so form S's a_acc is as universal as g†). Mock universes with a universal RAR, passed through "
      f"the SPARC error model and the same analysis, give {mt['tau_brown_16_50_84'][1]:.2f} and {mt['tau_rar_16_50_84'][1]:.2f} dex: "
      + ("the apparent excess is an artifact of the error estimates, and a universal scale suffices. " if art else
         "with this error model the data scatter more than a universal law would, g† as much as a_acc, so the excess is not "
         "specific to the stochastic remnant (an M/L that varies between galaxies by more than the 0.1 dex assumed could cause it). ") +
      f"Of 15 rank correlations with history proxies (Hubble type, gas fraction, surface brightness, disk scale length, orbits per "
      f"Hubble time), {nB_sig} survive the Holm correction, and {nP_sig} of the 15 partial correlations at fixed mass. Measured against the "
      f"correlations that a universal RAR already produces through the error model and shape mismatch (mock universes), {nS_sig + nSP_sig} "
      f"of 30 differ after Holm{(' (' + '; '.join(sig_list) + ')') if sig_list else ''}. "
      f"The signs a galaxy-specific accumulation predicts for log a_acc are met in {sum(1 for t in tB if t['sign_as_predicted'])} of 5, "
      f"and the slope of log a_acc on log N_orb is {h2['slope_log_a_vs_log_Norb']['slope']:+.2f} "
      f"[{h2['slope_log_a_vs_log_Norb']['boot_2.5_97.5'][0]:+.2f}, {h2['slope_log_a_vs_log_Norb']['boot_2.5_97.5'][1]:+.2f}] where a "
      "per-orbit random walk predicts +1. " + ("No history dependence beyond the global cosmic time is detected." if nS_sig + nSP_sig == 0 and
                                               nB_sig + nP_sig == 0 else "See R2 for what the surviving correlations do and do not imply."))
    def wb(v):
        return "better" if v < 0 else "worse"
    dN, dS_, dBu = (M[k]["BIC_total"] - M["rar_free"]["BIC_total"] for k in ("nfw_cm", "nfw_shmr", "burkert"))
    w(f"- **R3, contained remnant.** Baryons + a halo per galaxy fit better than any universal law in total BIC (NFW with the "
      f"Dutton-Macciò prior: {M['nfw_cm']['dBIC_total_vs_rar_univ']:+.0f} against the universal RAR; Burkert "
      f"{M['burkert']['dBIC_total_vs_rar_univ']:+.0f}), but they spend 2 parameters per galaxy ({M['nfw_cm']['k_total']}) against 1 in all. "
      "Under the point-wise likelihood any per-galaxy parameter absorbs galaxy-wide distance, inclination and M/L offsets: one free RAR "
      f"scale per galaxy already reaches {M['rar_free']['dBIC_total_vs_rar_univ']:+.0f}. Against that yardstick NFW is {wb(dN)} "
      f"(ΔBIC {dN:+.0f}), Burkert {wb(dBu)} ({dBu:+.0f}), and NFW halos held to the Moster et al. stellar-to-halo mass relation "
      f"{wb(dS_)} ({dS_:+.0f}). Per galaxy, NFW beats the universal RAR in {M['nfw_cm']['n_galaxies_better_than_rar_univ']} of "
      f"{h3['n_galaxies']}, Burkert in {M['burkert']['n_galaxies_better_than_rar_univ']}, cosmological NFW in "
      f"{M['nfw_shmr']['n_galaxies_better_than_rar_univ']}.")
    fs, fc, fn = F["nfw_shmr+sqrt"], F["nfw_shmr+const"], F["nfw_cm+sqrt"]

    def best_txt(f_):
        return "zero" if f_["best_at_zero"] else f"{p10(f_['log_A_best'])} m/s² (ΔBIC of adding it {f_['dBIC_add_term']:+.1f})"

    w(f"- **R4, the whole.** With NFW halos the best amplitude of the sqrt term is {best_txt(fn)}, and {best_txt(fs)} with cosmological "
      f"halos; its 95% upper bound is {p10(fn['log_A_95_upper'])} m/s² ({p10(fs['log_A_95_upper'])}; galaxy-bootstrap 84th percentile "
      f"of the bound {p10(fs['boot_log_A_95_16_50_84'][2])}), {1 / fs['A95_boot84_over_R1_value']:.0e} times smaller than the a_acc that "
      f"form B needs alone. A constant term has best amplitude {best_txt(F['nfw_cm+const'])} with NFW and {best_txt(fc)} with cosmological "
      f"halos, bounded at {p10(F['nfw_cm+const']['log_A_95_upper'])} and {p10(fc['log_A_95_upper'])}: "
      f"{fc['A95_over_R1_value']:.2f} of the constant that fits alone. With cored (Burkert) halos a small constant is preferred: "
      f"{best_txt(F['burkert+const'])}; since the same constant is not wanted with NFW halos, it reads as a correction to the halo's "
      "outer shape rather than a universal term (an interpretation). If primordial black holes are all of Ω_c h² = 0.120, halos "
      "exist, and the stochastic term has almost no room: at the bootstrap-84% bound it supplies a median "
      f"{100 * fs['A95_boot84_frac_of_dark_accel_outer_median']:.1f}% (sqrt) or {100 * fc['A95_boot84_frac_of_dark_accel_outer_median']:.0f}% "
      "(constant) of the dark acceleration at the outermost measured radius.")
    lw = z5["laws"]
    w(f"- **R5, cosmic time.** Accumulation makes a_acc grow with time; random-walk accumulation gives a_acc ∝ t, so at fixed rotation "
      f"speed galaxies at z ≈ 1 would need {lw['t (accumulation)']['1.0']['db_deep']:+.2f} dex more baryons (deep regime). The published "
      f"high-redshift kinematics point the other way: the baryonic Tully-Fisher zero point is offset by {UBLER17['db'][0]:+.2f} ± "
      f"{UBLER17['db_err'][0]:.2f} dex at z ≈ 0.9 and {UBLER17['db'][1]:+.2f} ± {UBLER17['db_err'][1]:.2f} at z ≈ 2.3 (Ubler et al. 2017), "
      f"and MUSE-DARK III finds the RAR's scale at z ≈ 1 a factor {z5['musedark_ratio_vs_local']:.1f} ± {z5['musedark_ratio_vs_local_err']:.1f} "
      f"above the local value. A scale ∝ H(z) ({lw['H(z)']['1.0']['ratio']:.2f} at z = 1) or ∝ 1/t ({lw['1/t']['1.0']['ratio']:.2f}) has the "
      f"right sign; 1/t gives {lw['1/t']['2.0']['ratio']:.1f} at z = 2, where Milgrom (2017) finds ~4 a0 all but excluded. These "
      "measurements carry systematics (gas masses, pressure support, model-dependent baryonic accelerations) of the size of the effect, "
      "and ΛCDM galaxy evolution produces such offsets too, so they are not a clean test; read literally, they disfavour accumulation.")
    w("- **R6.** The acoustic peaks, weak lensing, cluster masses and the Bullet Cluster need a relativistic theory of the stochastic "
      "remnant, which does not exist; nothing was fitted there. The contained remnant (primordial black holes as cold dark matter) covers "
      "them by construction.")
    w("")
    w("**Does a cohesive whole emerge?** Not as a combination. The two remnants compete for the same job. A universal stochastic term "
      "of form S reproduces the rotation curves as well as the RAR, but it is MOND with a new motivation: its scale matches cH0/2π only "
      "in the way Milgrom's a0 always has, it fails the solar system as written, its accumulation version has the wrong sign in time, and "
      "it has no relativistic form for the microwave background, lensing or clusters. The contained remnant covers the cosmology, and "
      "once its halos are present the data leave the stochastic term almost no room. The consistent reading is the contained remnant "
      "(cold dark matter, here primordial black holes) with a stochastic term too small to matter in galaxies, which inherits ΛCDM's "
      "galaxy-scale questions (cored inner profiles, the tightness of the RAR) rather than answering them.")
    w("")
    w("## Fixed before fitting, and chosen after seeing data")
    w("")
    w("Fixed in the script's header before any fit ran: the two forms B and S; the nine natural scales (the task's list); the five "
      "history proxies and the sign each should have under galaxy-specific accumulation; the halo models, their priors and bounds; the "
      "four evolution laws of R5 and the two acceleration regimes (deep, and g_obs = 3 and 10 g†) used to read the high-redshift data.")
    w("")
    w("Chosen or changed after seeing results, stated here:")
    w("")
    w("1. The R4 amplitude grid first started at 10⁻¹³ m/s². The first run showed that the sqrt term's bound lies below that, and that "
      "10⁻¹³ is not negligible for the sqrt form (√(10⁻¹² · 10⁻¹³) is 30% of g_bar at the lowest points). The grid now starts at 10⁻¹⁶, "
      "and the joint fitter's consistency check uses 10⁻³⁰ instead of 10⁻¹³. A resolution change, not a model change.")
    w("2. Two checks failed on the first run because the checks themselves were wrong (a log base in the finite-difference slope test; "
      "angle unwrapping in the orbit integration). Both were fixed; no tolerance was loosened.")
    w(f"3. The number of mock universes was raised from 200 to {o['n_mock']} after a test run, to steady the 2.5-97.5% null bands.")
    w(f"4. The mocks' extra per-point scatter (non-circular motions) is calibrated on the data: σ_x = {h2['sigma_x_mock_dex']:.3f} dex "
      f"makes the median per-galaxy reduced χ² of a free RAR fit match the data's {h2['median_red_chi2_data']:.2f}.")
    w("5. Using one free RAR scale per galaxy as the calibration for what per-galaxy freedom buys under the point-wise likelihood (R3) "
      "was decided after seeing that every per-galaxy model beats every universal one in total BIC.")
    w("6. The reading of the Burkert + constant improvement in R4 as a halo-shape correction is an interpretation made after seeing it.")
    w("7. The shift test of R2 (observed ρ minus the mock-null mean, against the data's bootstrap spread) and the mock calibration of "
      "the intrinsic scatter τ in R1c were added after test runs with 4 to 20 mocks, whose 95% bands looked much narrower than the "
      "bootstrap intervals. With 500 mocks the raw bands are about as wide as the bootstrap intervals and the partial ones narrower, "
      "because the mocks lack the data's extra scatter (R1c). Bands, shift test and the τ calibration are all reported.")
    w("")
    w("## Data and method")
    w("")
    w("- SPARC (Lelli, McGaugh and Schombert 2016), checked by SHA256 and not copied into the repository:")
    for k_, f_ in o["inputs"]["files"].items():
        w(f"  `{k_}`: `{f_['sha256']}`")
    w(f"- Sample of `sparc_rotation.py`: Q < 3, i ≥ 30°, δV/V < 0.1: {o['sample']['n_galaxies']} galaxies, {o['sample']['n_points']} "
      f"points, {o['sample']['n_galaxies_with_points']} galaxies with points; Υ_disk = 0.5, Υ_bulge = 0.7. Per-galaxy work uses the "
      f"{h3['n_galaxies']} galaxies with at least 5 points ({h3['n_points']} points).")
    w("- Likelihood L1 (primary, from `sparc_rotation.py`): Gaussian in log g_obs; the variance is the full error model of Lelli et al. "
      "(2017), with the g_bar error carried through each model's slope. L2: velocity errors plus a fitted intrinsic floor. Robust: "
      "soft-L1 loss. BIC = -2 ln L + k ln N over points. Galaxies are resampled for every uncertainty, because points within a galaxy "
      "share distance, inclination and M/L errors and the point-wise BIC overstates the evidence.")
    w("- Per-galaxy scales (R1c, R2) are fitted as in `sparc_rotation.py` S2c: velocity errors per point, with distance, inclination, "
      "Υ (±25%) and HI (±10%) applied as whole-galaxy shifts and added in quadrature.")
    w("- Halos (R3, R4): NFW in (M200, c200) with ρ_crit for H0 = 67.4 and the Dutton and Macciò (2014) relation log c200 = 0.905 - "
      "0.101 log(M200/10¹² h⁻¹ Msun), 0.11 dex scatter, as a prior; \"cosmological\" NFW halos also carry the Moster, Naab and White "
      "(2013) stellar-to-halo mass relation (0.15 dex) with M* = 0.5 L[3.6]; Burkert halos in (ρ0, r0) without prior. Each galaxy is fitted "
      "on a grid and refined by Nelder-Mead (MAP); BIC uses -2 ln L at the MAP and k = 2 per galaxy.")
    w("- R4 adds one universal term, A (constant) or √(g_bar A), to baryons + halo, refits every halo at each of "
      f"{len(h4['grid_log_A'])} amplitudes from 10⁻¹⁶ to 10^{h4['grid_log_A'][-1]:.1f} m/s², and sums -2 ln (L × prior) over galaxies "
      "(profile likelihood). The one-sided 95% bound is where the sum rises by 2.71; galaxies are resampled for its spread.")
    w("")
    w("## R1a: one universal a_acc")
    w("")
    w("| model | free | best value [m/s²] (bootstrap 16-84%) | χ²/dof | ΔBIC vs RAR (L1) | σ_int (L2) [dex] | ΔBIC vs RAR (L2) | robust MAD [dex] |")
    w("|---|---|---|---|---|---|---|---|")
    for k in ("newton", "rar", "const", "brown", "simple"):
        e = a[k]
        val = "-" if k == "newton" else f"{e2(e['best'])} ({e2(e['boot_16_50_84'][0])} to {e2(e['boot_16_50_84'][2])})"
        w(f"| {LABEL[k]} | {e['k']} | {val} | {e['chi2_per_dof']:.3f} | {e['dBIC_vs_rar']:+.1f} | {e['L2']['sigma_int_dex']:.3f} | "
          f"{e['L2']['dBIC_vs_rar']:+.1f} | {e['robust']['mad_dex']:.3f} |")
    w("")
    w("Median residual log(g_obs/g_model) in dex, by acceleration range:")
    w("")
    w("| model | g_bar < 1e-11 | 1e-11 to 1e-10 | 1e-10 to 1e-9 | > 1e-9 |")
    w("|---|---|---|---|---|")
    for k in ("rar", "const", "brown", "simple"):
        r_ = a[k]["median_resid_dex"]
        w(f"| {k} | {r_['gbar<1e-11']:+.3f} | {r_['1e-11..1e-10']:+.3f} | {r_['1e-10..1e-9']:+.3f} | {r_['gbar>1e-9']:+.3f} |")
    w("")
    gc = a["galaxy_counts"]
    rs = a["residual_slope"]
    w(f"- Galaxy by galaxy (lower -2 ln L under the universal fits, {gc['n_galaxies']} galaxies): RAR over B in {gc['rar_beats_brown']}, "
      f"RAR over S in {gc['rar_beats_simple']}, S over B in {gc['simple_beats_brown']}, B over the constant in {gc['brown_beats_const']}, "
      f"S over the constant in {gc['simple_beats_const']}.")
    w(f"- Low-acceleration slope of log(g_obs - g_bar) in the bins of `sparc_rotation.py` S2d: data {rs['data']:.3f}; RAR {rs['rar']:.3f}; "
      f"form B {rs['brown']:.3f} (exactly 1/2 by construction); form S {rs['simple']:.3f}; constant 0.")
    w("")
    w("**Solar system.** Both forms are pointwise laws in g_bar. In the Sun's field the extra force of form B is √(GM a_acc)/r (an extra "
      "log potential), and that of form S tends to the constant a_acc. A small radial force k rⁿ advances the perihelion by -π(n+2)ε per "
      "orbit, ε being its ratio to GM/r² (checked here by integrating an orbit). Against the extra perihelion precessions allowed by the "
      "EPM2011 ephemerides (Pitjeva and Pitjev 2013, Table 4; their uncertainties taken as bounds):")
    w("")
    w("| planet | g_sun [m/s²] | form B [mas/yr] | × bound | form S [mas/yr] | × bound | bound [mas/yr] |")
    w("|---|---|---|---|---|---|---|")
    for pl, r_ in a["solar_system"].items():
        w(f"| {pl} | {r_['g_sun']:.2e} | {r_['brown']['precession_mas_per_yr']:+.2e} | {r_['brown']['over_bound']:.0e} | "
          f"{r_['simple']['precession_mas_per_yr']:+.2e} | {r_['simple']['over_bound']:.0e} | {PITJEVA[pl][1]} |")
    w("")
    w(f"The RAR function switches off exponentially (its excess at Saturn is of order 10^{a['solar_system']['Saturn']['rar_log10_dg_over_g']:.0f} "
      "of g), so the RAR itself is untouched; MOND's external-field effect is a separate issue not treated here.")
    w("")
    w("## R1b: parameter-free scales")
    w("")
    w(f"Systematics on log a_acc: galaxy bootstrap {B['sigma_boot_dex']:.3f} (B) and {Sf['sigma_boot_dex']:.3f} (S) dex; stellar M/L "
      f"shifted by ±0.1 dex: {B['sigma_ups_dex']:.3f} and {Sf['sigma_ups_dex']:.3f}; likelihood choice (L1, L2, robust): "
      f"{B['sigma_method_dex']:.3f} and {Sf['sigma_method_dex']:.3f}; total {B['sigma_tot_dex']:.3f} and {Sf['sigma_tot_dex']:.3f} dex. "
      f"SPARC's 97 Hubble-flow distances assume H0 = 73; rescaled to 67.4 they give a_acc = {e2(B['best_H0_67.4'])} (B) and "
      f"{e2(Sf['best_H0_67.4'])} (S). Each H0 = 67.4 candidate is compared with the rescaled data, each H0 = 73 candidate and c/t0 with "
      "SPARC's own distances. ΔBIC is against the form's own best fit on the same data (a fixed scale has k = 0).")
    w("")
    w("| candidate | value [m/s²] | B: a_acc / candidate | B: ΔBIC | S: a_acc / candidate | S: ΔBIC | RAR g† / candidate |")
    w("|---|---|---|---|---|---|---|")
    for name, val in b["candidates"].items():
        rb_, rs_ = B["candidates"][name], Sf["candidates"][name]
        w(f"| {name} | {e2(val)} | {rb_['best_over_candidate']:.3f} | {rb_['dBIC_vs_best']:+.1f} | {rs_['best_over_candidate']:.3f} | "
          f"{rs_['dBIC_vs_best']:+.1f} | {b['rar_gdag_over_candidates'][name]['best_over_candidate']:.3f} |")
    w("")
    w(f"**Look-elsewhere.** The {leS['n_candidates']} candidates span {leS['span_dex']:.2f} dex with a median spacing of "
      f"{leS['median_spacing_dex']:.3f} dex; they form two clusters (with and without 2π) a factor 2π apart. For form S the nearest is "
      f"{leS['nearest']} at {leS['nearest_dex']:.3f} dex ({leS['nearest_in_sigma_tot']:.2f} σ_tot); {leS['n_within_2sigma_tot']} candidates "
      f"lie within 2σ_tot. A log-uniform scale within ±1 dex of the fitted value lands within {leS['nearest_dex']:.3f} dex of some "
      f"candidate with probability {leS['p_as_close_in_2dex_window']:.2f}, and within 1σ_tot with probability "
      f"{leS['p_within_1sigma_tot_in_2dex_window']:.2f}. For form B: nearest {leB['nearest']} at {leB['nearest_dex']:.3f} dex, probability "
      f"{leB['p_as_close_in_2dex_window']:.2f}, {leB['n_within_2sigma_tot']} candidates within 2σ. The measurement cannot pick one of "
      "the 2π-scales over another, and picking the closest after the fit is not a test. The match a0 ≈ cH0/2π is Milgrom's "
      "(1983) observation, not a consequence of the accumulation hypothesis, which gives no factor 2π. The scales without 2π, which a "
      "horizon argument would give (cH0, cH_inf = Bridge A, c/t0), are excluded.")
    w("")
    w("## R1c: a_acc per galaxy")
    w("")
    w("| per-galaxy scale | median [m/s²] | spread [dex] | median error [dex] | intrinsic scatter τ [dex] (68%) | Δ(-2 ln L) of τ = 0 | Spearman vs log M_bar | slope vs log M_bar (16-84%) |")
    w("|---|---|---|---|---|---|---|---|")
    for k, lab in (("brown", "a_acc, form B"), ("simple", "a_acc, form S"), ("rar", "g†, RAR")):
        e = cc[k]
        w(f"| {lab} | {e2(e['percentiles_16_50_84'][1])} | {e['std_dex']:.3f} | {e['median_sigma_tot_dex']:.3f} | {e['tau_ml_dex']:.3f} "
          f"({e['tau_68'][0]:.3f} to {e['tau_68'][1]:.3f}) | {e['dm2lnL_tau0']:.1f} | {e['spearman_logMbar'][0]:+.2f} (p = {e['spearman_logMbar'][1]:.1e}) | "
          f"{e['slope_vs_logMbar']:+.3f} ({e['slope_boot_16_84'][0]:+.3f} to {e['slope_boot_16_84'][1]:+.3f}) |")
    w("")
    sc = cc["shape_counts"]
    mt = h2["spread_mock_dex"]["rar"]
    w(f"- Against the per-galaxy error estimates (stat ⊕ whole-galaxy shifts) {'none of the three scales is' if tau_all else 'not every scale is'} "
      f"consistent with a single value without extra scatter; the RAR's g† (τ = {cc['rar']['tau_ml_dex']:.2f} dex) scatters as much as "
      f"form S's a_acc (τ = {cc['simple']['tau_ml_dex']:.2f}). But the same estimator applied to mock universes with a universal RAR "
      f"gives τ = {mt['tau_brown_16_50_84'][1]:.2f} ({mt['tau_brown_16_50_84'][0]:.2f} to {mt['tau_brown_16_50_84'][2]:.2f}) for a_acc and "
      f"{mt['tau_rar_16_50_84'][1]:.2f} ({mt['tau_rar_16_50_84'][0]:.2f} to {mt['tau_rar_16_50_84'][2]:.2f}) for g†. "
      + ("The data's τ is within what a universal law produces through the error model; the quadrature estimates understate the "
         "per-galaxy errors. " if art else
         "The data's τ is above what a universal law produces through this error model (Υ varying by 0.1 dex between galaxies, the "
         "catalogue's distance and inclination errors, HI at 10%), for g† as much as for a_acc of form S: either the error model "
         "misses a galaxy-level term, such as a larger spread of M/L, or neither scale is universal. ") +
      "Li, Lelli, McGaugh and Schombert (2018), who marginalise each galaxy over M/L, distance and inclination, find no credible "
      "variation of g†; Rodrigues et al. (2018) argue the opposite with a different treatment. On this question form S and the RAR "
      f"stand or fall together. Mass trends (Spearman): form B {cc['brown']['spearman_logMbar'][0]:+.2f}, form S {cc['simple']['spearman_logMbar'][0]:+.2f}, "
      f"RAR {cc['rar']['spearman_logMbar'][0]:+.2f}; a falling a_acc of form B with mass is what its overshoot at high acceleration would "
      "produce in massive, high-acceleration galaxies.")
    w(f"- Shape within galaxies (one free scale per galaxy, velocity errors, {sc['n_points']} points): χ² = {sc['chi2_sum']['rar']:.0f} (RAR), "
      f"{sc['chi2_sum']['simple']:.0f} (S), {sc['chi2_sum']['brown']:.0f} (B); the RAR shape is better than B in {sc['rar_beats_brown']} "
      f"and than S in {sc['rar_beats_simple']} of {cc['n_galaxies']} galaxies.")
    w("")
    w("## R2: history dependence")
    w("")
    w("A universal a_acc carries no history beyond the global cosmic time. A galaxy-specific accumulation would make older, more evolved, "
      "dynamically older systems carry a larger a_acc: negative correlations with Hubble type, gas fraction and disk scale length, positive "
      "ones with surface brightness and with N_orb, the orbits completed at the outermost radius in 13.8 Gyr (median "
      f"{h2['Norb_percentiles_16_50_84'][1]:.0f}, 16-84%: {h2['Norb_percentiles_16_50_84'][0]:.0f} to {h2['Norb_percentiles_16_50_84'][2]:.0f}); "
      "a fixed variance per orbit gives a_acc ∝ N_orb. Spearman ρ with the galaxy-bootstrap 95% interval, Holm-adjusted p over all 30 "
      "tests (15 raw, 15 partial at fixed log M_bar), and the 95% band of ρ in mock universes in which the true law is the universal RAR "
      "(null R) or the universal form B (null B), observed through the SPARC error model. The last column tests the shift of the observed "
      "ρ (raw / partial) from the null-R mean against the data's own bootstrap spread, Holm-adjusted over all 30:")
    w("")
    w("| quantity | proxy | ρ (95%) | p (Holm) | null R | null B | partial ρ (95%) | p (Holm) | null R | shift from null R: p (Holm), raw / partial |")
    w("|---|---|---|---|---|---|---|---|---|---|")
    for t in h2["tests"]:
        w(f"| {t['quantity']} | {t['proxy']} | {t['rho']:+.2f} ({t['rho_boot_2.5_97.5'][0]:+.2f}, {t['rho_boot_2.5_97.5'][1]:+.2f}) | "
          f"{t['p_holm']:.2g} | {t['null_rar_rho_2.5_97.5'][0]:+.2f} to {t['null_rar_rho_2.5_97.5'][1]:+.2f} | "
          f"{t['null_brown_rho_2.5_97.5'][0]:+.2f} to {t['null_brown_rho_2.5_97.5'][1]:+.2f} | {t['partial_rho']:+.2f} "
          f"({t['partial_boot_2.5_97.5'][0]:+.2f}, {t['partial_boot_2.5_97.5'][1]:+.2f}) | {t['partial_p_holm']:.2g} | "
          f"{t['null_rar_partial_2.5_97.5'][0]:+.2f} to {t['null_rar_partial_2.5_97.5'][1]:+.2f} | "
          f"{t['shift_p_holm']:.2g} / {t['partial_shift_p_holm']:.2g} |")
    w("")
    sN = h2["slope_log_a_vs_log_Norb"]
    w(f"- Significant after Holm (p < 0.05): {nB_sig} of 15 raw and {nP_sig} of 15 partial correlations against zero; {nS_sig} raw and "
      f"{nSP_sig} partial against the null-R mean. Outside the null-R 95% band: {nB_out} of 15 raw and {nP_out} of 15 partial ρ "
      "(about 0.75 of 15 expected by chance). The bands come from mocks that lack the extra galaxy-to-galaxy scatter of R1c "
      f"(error-weighted τ of g† {h2['spread_mock_dex']['rar']['tau_rar_16_50_84'][1]:.2f} dex in the mocks against "
      f"{cc['rar']['tau_ml_dex']:.2f} in the data), so they understate the null spread of the partial correlations; the shift test, "
      "which uses the data's own bootstrap spread, is the fair one, and after Holm it finds no departure. The two with the smallest Holm p: "
      + "; ".join(f"{t['quantity'].split(' (')[0]} vs {t['proxy']}, partial ρ {t['partial_rho']:+.2f} (Holm p {t['partial_shift_p_holm']:.2g})"
                  for t in sorted(h2["tests"], key=lambda t: t["partial_shift_p_holm"])[:2]) + ".")
    w(f"- log a_acc (form B) against log N_orb: slope {sN['slope']:+.3f} (95%: {sN['boot_2.5_97.5'][0]:+.3f} to {sN['boot_2.5_97.5'][1]:+.3f}); "
      "a per-orbit random walk predicts +1, a universal scale 0.")
    w("- The null means are not zero. A universal law observed through the error model, and fitted per galaxy with a shape that differs "
      "from the truth, already correlates with proxies that track where on the g_bar axis a galaxy's points lie (mass, surface "
      "brightness, gas fraction). A correlation is evidence for history only if it departs from that baseline; and the mocks contain only "
      "the error terms listed (no M/L variation correlated with type, no non-Gaussian outliers), so even a departure would first point to "
      "an unmodelled systematic before it pointed to history.")
    w("")
    w("## R3: the contained remnant (halos)")
    w("")
    w(f"Per-galaxy fits on the {h3['n_galaxies']} galaxies, likelihood L1 for every model. Universal models carry their one global "
      "parameter from the fit to all points; per-galaxy BIC counts k = 0 for them, 1 for a free scale, 2 for a halo.")
    w("")
    w("| model | parameters (total) | -2 ln L | ΔBIC (total) vs universal RAR | galaxies better than universal RAR | than universal B |")
    w("|---|---|---|---|---|---|")
    labs = {"rar": "RAR, universal g†", "simple": "form S, universal a_acc", "brown": "form B, universal a_acc", "const": "constant, universal",
            "rar_free": "RAR, g† per galaxy", "brown_free": "form B, a_acc per galaxy", "nfw_cm": "NFW + c-M prior",
            "nfw_shmr": "NFW + c-M + stellar-to-halo prior", "burkert": "Burkert"}
    for k, lab in labs.items():
        e = M[k]
        w(f"| {lab} | {e['k_total']} | {e['m2lnL']:.1f} | {e['dBIC_total_vs_rar_univ']:+.1f} | {e['n_galaxies_better_than_rar_univ']} | "
          f"{e['n_galaxies_better_than_brown_univ']} |")
    w("")
    w(f"- Halo parameters (16/50/84%): NFW log M200 {M['nfw_cm']['param_percentiles_16_50_84'][0][0]:.2f} / "
      f"{M['nfw_cm']['param_percentiles_16_50_84'][0][1]:.2f} / {M['nfw_cm']['param_percentiles_16_50_84'][0][2]:.2f}, log c200 "
      f"{M['nfw_cm']['param_percentiles_16_50_84'][1][0]:.2f} / {M['nfw_cm']['param_percentiles_16_50_84'][1][1]:.2f} / "
      f"{M['nfw_cm']['param_percentiles_16_50_84'][1][2]:.2f}; median log(M200/M_bar) {M['nfw_cm']['median_log_M200_over_Mbar']:.2f} "
      f"(with the stellar-to-halo prior {M['nfw_shmr']['median_log_M200_over_Mbar']:.2f}). Fits at a parameter bound: NFW "
      f"{M['nfw_cm']['n_at_bounds']}, cosmological NFW {M['nfw_shmr']['n_at_bounds']}, Burkert {M['burkert']['n_at_bounds']}.")
    w("- The point-wise likelihood treats the galaxy-wide distance and inclination errors as independent per point, so any per-galaxy "
      "parameter gains by absorbing them. One free RAR scale per galaxy is the fair yardstick for what such freedom buys: against it "
      f"NFW (+c-M) has ΔBIC {M['nfw_cm']['BIC_total'] - M['rar_free']['BIC_total']:+.0f}, cosmological NFW "
      f"{M['nfw_shmr']['BIC_total'] - M['rar_free']['BIC_total']:+.0f}, Burkert {M['burkert']['BIC_total'] - M['rar_free']['BIC_total']:+.0f}. "
      f"Cored halos fit better than cuspy ones with the same parameter count (Burkert against NFW: ΔBIC "
      f"{M['burkert']['BIC_total'] - M['nfw_cm']['BIC_total']:+.0f}), the known cusp-core issue. The halos accommodate the RAR's "
      "one-parameter regularity with two parameters per galaxy; they do not predict it.")
    w("")
    w("## R4: halos and a universal stochastic term together")
    w("")
    w("| halo + term | best A [m/s²] | Δ(-2 ln L) best - zero | ΔBIC of adding the term | 95% bound on A | bootstrap 50 / 84% of the bound | best at A = 0 in resamples | bound / R1 value | share of dark acceleration at outer radius (at bootstrap-84% bound) |")
    w("|---|---|---|---|---|---|---|---|---|")
    for key, f_ in F.items():
        best = "0" if f_["best_at_zero"] else e2(10 ** f_["log_A_best"])
        share = f_.get("A95_boot84_frac_of_dark_accel_outer_median")
        w(f"| {key} | {best} | {f_['dm2lnL_best_minus_zero']:+.1f} | {f_['dBIC_add_term']:+.1f} | {p10(f_['log_A_95_upper'])} | "
          f"{p10(f_['boot_log_A_95_16_50_84'][1])} / {p10(f_['boot_log_A_95_16_50_84'][2])} | {100 * f_['boot_frac_best_at_zero']:.0f}% | "
          f"{f_.get('A95_over_R1_value', float('nan')):.1e} | {'-' if share is None else f'{100 * share:.1f}%'} |")
    w("")
    w(f"R1 values for comparison: a_acc = {e2(a['brown']['best'])} m/s² for the sqrt form (form B alone) and |γ1|/2 = {e2(a['const']['best'])} "
      "for the constant alone. Where the best amplitude is zero, the summed -2 ln L rises roughly as √A from zero (`dm2lnL_curve` in the "
      "JSON): the halos, refitted at each A, cannot absorb the term, so it costs at first order and the bound is far below the "
      "value the term needs on its own. "
      + (f"With Burkert halos the preferred constant is {F['burkert+const']['best_over_R1_value']:.2f} of the value that replaces the halos."
         if not F["burkert+const"]["best_at_zero"] else ""))
    w("")
    w("**Consistency requirement.** The microwave background needs Ω_c h² = 0.120 ± 0.001 of collisionless matter at z ≈ 1100 (Planck "
      "2018). If that is the contained remnant, halos of the cosmological masses exist around galaxies, and the stochastic term must "
      "not double count the dark acceleration they already supply. The bounds above are that room: with cosmological NFW halos the sqrt "
      f"term can supply at most a median {100 * fs['A95_boot84_frac_of_dark_accel_outer_median']:.1f}% of the dark acceleration at the "
      f"outermost measured radius (galaxy-bootstrap 84th percentile of the bound), the constant {100 * fc['A95_boot84_frac_of_dark_accel_outer_median']:.0f}%.")
    w("")
    w("## R5: evolution with cosmic time")
    w("")
    w(f"Flat ΛCDM with Ω_m = 0.315, Ω_Λ = 0.685, H0 = 67.4 (t0 = {z5['t0_LCDM_Gyr']:.2f} Gyr without radiation). In the deep regime "
      "v⁴ = G M a, so at fixed rotation speed log M_bar(z) - log M_bar(0) = -log(a(z)/a(0)). The high-redshift disks are not in the deep "
      "regime (Milgrom 2017 puts the z ≈ 1-2.4 galaxies of Genzel et al. at 3-11 a0 at their half-light radii), so the table also gives the "
      "shift for a RAR-shaped law at fixed V and R with g_obs = 3 g† and 10 g†, where any change of scale is diluted.")
    w("")
    w("| law for a_acc(z) | a(z)/a(0) at z = 0.9 / 1 / 2 / 2.3 | Δlog M_bar, deep, z = 0.9 / 2.3 | at g_obs = 3 g† | at 10 g† |")
    w("|---|---|---|---|---|")
    for lw_, e in z5["laws"].items():
        w(f"| {lw_} | {e['0.9']['ratio']:.2f} / {e['1.0']['ratio']:.2f} / {e['2.0']['ratio']:.2f} / {e['2.3']['ratio']:.2f} | "
          f"{e['0.9']['db_deep']:+.2f} / {e['2.3']['db_deep']:+.2f} | {e['0.9']['db_x3']:+.2f} / {e['2.3']['db_x3']:+.2f} | "
          f"{e['0.9']['db_x10']:+.2f} / {e['2.3']['db_x10']:+.2f} |")
    w("")
    ui = z5["ubler_implied_ratio"]
    w("Published measurements (numbers verified against the papers' text):")
    w("")
    w(f"- **Ubler et al. (2017), KMOS3D.** Baryonic Tully-Fisher relation with the slope fixed at 3.75 (Lelli et al. 2016), zero-point "
      f"offsets from the local relation Δb = {UBLER17['db'][0]} ± {UBLER17['db_err'][0]} dex at z ≈ 0.9 ({UBLER17['n'][0]} galaxies) and "
      f"{UBLER17['db'][1]} ± {UBLER17['db_err'][1]} at z ≈ 2.3 ({UBLER17['n'][1]}); without their pressure-support correction "
      f"{UBLER17['db_no_pressure'][0]} and {UBLER17['db_no_pressure'][1]}. Baryonic masses carry ~0.15 dex each (stellar 0.15, gas 0.20, "
      "Chabrier IMF); gas masses come from scaling relations and omit atomic gas; the velocity is the model's peak, assumed comparable to "
      "the local Vflat. The errors quoted are statistical only. Read as a change of scale they imply a(z)/a(0) = "
      f"{ui['0.9']['deep']:.1f} (deep) to {ui['0.9']['x3']:.1f} (3 g†) at z ≈ 0.9 and {ui['2.3']['deep']:.1f} to {ui['2.3']['x3']:.1f} at "
      "z ≈ 2.3: non-monotonic, so no single law fits both, and the authors explain the offsets in ΛCDM by evolving gas and dark matter "
      "fractions.")
    w(f"- **MUSE-DARK III (Ciocan et al. 2026).** The RAR of {MUSEDARK['n']} star-forming galaxies at {MUSEDARK['z_lo']} < z < "
      f"{MUSEDARK['z_hi']}: a0(z ≈ 1) = 2.38 (+0.12, -0.10) × 10⁻¹⁰ m/s², a factor {z5['musedark_ratio_vs_local']:.2f} ± "
      f"{z5['musedark_ratio_vs_local_err']:.2f} above the local 1.2 ± 0.26; their linear fit a0(z) = 1.0 + 1.59 z (10⁻¹⁰ m/s²) gives "
      f"{z5['musedark_ratio_own_fit']:.2f} at z = 1. Caveats they state: a_tot and a_bar come from the same 3D model, molecular gas adds "
      "~0.2 dex of systematic uncertainty, and the linear form is phenomenological.")
    w("- **Milgrom (2017)**, on the six rotation curves of Genzel et al. (2017) at z ≈ 0.9-2.4: the data \"all but exclude\" a MOND constant "
      "of ~4 a0 at z ≈ 2 and exclude a0 ∝ (1+z)^3/2.")
    w(f"- **RC100 (Nestor Shachar et al. 2023)**: dark-matter fractions within R_e of 0.38 ± 0.23 (z = 0.6-1.2, 33 galaxies) and "
      "0.27 ± 0.18 (z = 1.2-2.5, 67), quoted as median ± scatter; not turned into an a(z) here, because that needs each galaxy's own "
      "g_bar. Del Popolo and Chan (2024) use a0 estimates for these galaxies and find, with large uncertainties, an anti-correlation "
      "with z within that sample. MIGHTEE-HI (Vărăşteanu et al. 2025) reports tentative evolution with 19 galaxies at z < 0.08, where every law here changes "
      "a by less than 10%.")
    w("")
    w(f"Comparison: at z = 1, MUSE-DARK's {z5['musedark_ratio_vs_local']:.1f} ± {z5['musedark_ratio_vs_local_err']:.1f} sits between "
      f"H(z) ({z5['laws']['H(z)']['1.0']['ratio']:.2f}) and 1/t ({z5['laws']['1/t']['1.0']['ratio']:.2f}); accumulation "
      f"({z5['laws']['t (accumulation)']['1.0']['ratio']:.2f}) and a constant are below it. At z = 2, 1/t ({z5['laws']['1/t']['2.0']['ratio']:.1f}) "
      "meets Milgrom's exclusion of ~4 a0. The Ubler offsets have the sign of a scale that was larger in the past, opposite to "
      "accumulation. Read in the deep regime, the offset at z ≈ 0.9 is larger and the one at z ≈ 2.3 smaller than either falling law "
      "predicts, and the implied ratio falls between z ≈ 0.9 and 2.3, which no monotonic law does. The two time arrows disagree in "
      "principle: an accumulated quantity grows with time, while the cosmological coincidence scales cH and c/t fall. Matching a_acc(t0) "
      "to cH0/2π and making it accumulate cannot both hold except as a coincidence of the present epoch.")
    w("")
    w("## R6: what cannot be fitted")
    w("")
    w("- **Microwave background.** The acoustic peaks need Ω_c h² = 0.120 of pressureless matter at z ≈ 1100, with the baryons already "
      "at their present share. A stochastic term in the Newtonian limit of a static, spherical calculation has no cosmological "
      "perturbation theory: there is no prediction for the peaks to fit. The contained remnant is cold dark matter and fits them as ΛCDM "
      "does.")
    w("- **Weak and strong lensing.** Light deflection needs the metric, not only the Newtonian potential; Oppenheim and Russo state "
      "that lensing is not yet addressed. Nothing to fit. Halos lens as in ΛCDM.")
    w("- **Cluster masses.** MOND-like laws reduce the clusters' mass discrepancy but do not remove it (Sanders 2003: the discrepancy "
      "becomes three to four times smaller than with Newtonian dynamics). Forms B and S inherit that residual; a cluster test would need "
      "the X-ray and lensing profiles and was not run.")
    w("- **Bullet Cluster.** The lensing mass of 1E0657-558 follows the galaxies, offset from the X-ray gas at 8σ (Clowe et al. 2006). "
      "A term that depends only on the local baryonic field points at the gas; collisionless halos follow the galaxies, as observed.")
    w("- **The solar system** (R1a) is the one regime outside galaxies where the forms make a definite prediction, and it fails.")
    w("")
    w("## Caveats")
    w("")
    w("- All fits use Υ_disk = 0.5 and Υ_bulge = 0.7 (as `sparc_rotation.py`), M* = 0.5 L[3.6] for the stellar-to-halo prior (bulge "
      "light included at the disk value), and the point-wise likelihood L1, which overstates differences between models; the galaxy "
      "bootstrap is the conservative measure.")
    w("- Halos are fitted with fixed Υ; letting Υ float with a prior (as published halo catalogues do) improves halo fits, and would also "
      "improve the universal laws. The Moster et al. relation was derived with a WMAP7 cosmology; how well it is constrained at the "
      "lowest stellar masses of SPARC was not checked here. NFW halos are not adiabatically contracted.")
    w("- The high-redshift comparison uses published summary numbers; their systematic uncertainties are comparable to the predicted "
      "effects, and their samples are massive, baryon-dominated star-forming disks selected differently from SPARC.")
    w("- The accumulation hypothesis is not derived from the classical-quantum dynamics: Oppenheim and Russo's mean metric is static and "
      "spherically symmetric, and their linear term is fixed by a boundary condition, not by a history.")
    w("")
    w("## Reproduce")
    w("")
    w("```")
    w("python3 docs/simulation/remnant_history.py --data <dir with MassModels_Lelli2016c.mrt and SPARC_Lelli2016c.mrt>")
    w("```")
    w("")
    w("Needs numpy, scipy and matplotlib and `docs/simulation/sparc_rotation.py` next to it. `--boot N` and `--mock N` set the resample "
      "counts. Deterministic (fixed seeds, one BLAS thread); a few minutes on one core and well under 1 GB of memory.")
    w("")
    w("## References")
    w("")
    w("Marked *verified* where the record and the numbers used were checked on 2026-10-31 against the arXiv text or record, the publisher "
      "page or ADS, by web search.")
    w("")
    refs = [
        "F. Lelli, S. S. McGaugh, J. M. Schombert, *SPARC: Mass Models for 175 Disk Galaxies with Spitzer Photometry and Accurate Rotation "
        "Curves*, AJ 152, 157 (2016), arXiv:1606.09251. *Verified*: 97 Hubble-flow distances on H0 = 73 km/s/Mpc (the table has 97 with f_D = 1).",
        "S. S. McGaugh, F. Lelli, J. M. Schombert, PRL 117, 201101 (2016), arXiv:1609.05917; F. Lelli et al., ApJ 836, 152 (2017), "
        "arXiv:1610.08981. Cuts, RAR function and error model, as verified in `sparc_rotation.md`.",
        "J. Oppenheim, A. Russo, *Anomalous contribution to galactic rotation curves due to stochastic spacetime*, arXiv:2402.19459 (v3, "
        "22 July 2024; no journal reference). *Verified* (record): static, spherically symmetric, further study needed.",
        "Planck Collaboration, *Planck 2018 results. VI. Cosmological parameters*, A&A 641, A6 (2020), arXiv:1807.06209. *Verified*: "
        "H0 = 67.4 ± 0.5, Ω_m = 0.315 ± 0.007, Ω_c h² = 0.120 ± 0.001. (Ω_Λ = 0.685 is 1 - Ω_m.)",
        "A. A. Dutton, A. V. Macciò, *Cold dark matter haloes in the Planck era*, MNRAS (2014), doi:10.1093/mnras/stu742, "
        "arXiv:1402.7073. *Verified*: Eq. 8, log c200 = 0.905 - 0.101 log(M200/10¹² h⁻¹ Msun) at z = 0, scatter 0.11 dex, Planck h = 0.671.",
        "B. P. Moster, T. Naab, S. D. M. White, *Galactic star formation and accretion histories from matching galaxies to dark matter "
        "haloes*, MNRAS 428, 3121 (2013), arXiv:1205.5807. *Verified*: Eq. 2 and Table 1 (log M1 = 11.590, N = 0.0351, β = 1.376, γ = 0.608), "
        "0.15 dex scatter, M200c, Chabrier IMF, WMAP7.",
        "E. V. Pitjeva, N. P. Pitjev, *Relativistic effects and dark matter in the Solar system from observations of planets and "
        "spacecraft*, MNRAS 432, 3431 (2013), arXiv:1306.3043. *Verified*: Table 4, extra perihelion precessions (Mars -0.00020 ± 0.00037, "
        "Saturn -0.0032 ± 0.0047 mas/yr).",
        "H. Ubler et al., *The evolution of the Tully-Fisher relation between z ~ 2.3 and z ~ 0.9 with KMOS3D*, ApJ 842, 121 (2017), "
        "arXiv:1703.04321. *Verified*: Table 2, Fig. 5 and Sects. 2.2, 4.2, 4.3 (Δb = -0.44 and -0.27 dex, ±0.04 and ±0.05; -0.33 and "
        "-0.09 without pressure support; mass uncertainties).",
        "B. I. Ciocan et al., *MUSE-DARK III: The evolution of the radial acceleration relation at intermediate redshifts*, A&A 709, L16 "
        "(2026), arXiv:2604.22613. *Verified*: a0(z~1) = 2.38 (+0.12, -0.10) × 10⁻¹⁰ m/s², a0(z) = 1.0 + 1.59 z, local 1.2 ± 0.26, caveats.",
        "M. Milgrom, *High-redshift rotation curves and MOND*, arXiv:1703.06110 (v3, 2017). *Verified* (abstract): 3-11 a0 at half-light "
        "radii; ~4 a0 at z ~ 2 all but excluded; a0 ∝ (1+z)^3/2 excluded.",
        "A. Nestor Shachar et al., *RC100: Rotation Curves of 100 Massive Star-forming Galaxies at z = 0.6-2.5 Reveal Little Dark Matter "
        "on Galactic Scales*, ApJ 944, 78 (2023), arXiv:2209.12199. *Verified*: f_DM(R_e) medians 0.38 ± 0.23 and 0.27 ± 0.18, bins and counts.",
        "A. Del Popolo, M. H. Chan, *On the time dependency of a0*, Phys. Dark Univ. 43, 101393 (2024), arXiv:2405.01841. *Verified* (abstract).",
        "A. A. Vărăşteanu et al., *MIGHTEE-HI: The radial acceleration relation with resolved stellar mass measurements*, MNRAS (2025), "
        "doi:10.1093/mnras/staf1079, arXiv:2504.20857. *Verified* (abstract): 19 galaxies to z = 0.08, tentative evolution.",
        "P. Li, F. Lelli, S. S. McGaugh, J. M. Schombert, *Fitting the radial acceleration relation to individual SPARC galaxies*, A&A 615, "
        "A3 (2018), arXiv:1803.00022. *Verified* (abstract): no credible variation of the acceleration scale.",
        "D. C. Rodrigues, V. Marra, A. del Popolo, Z. Davari, *Absence of a fundamental acceleration scale in galaxies*, Nat. Astron. 2, 668 "
        "(2018), arXiv:1806.06803. *Verified* (abstract).",
        "R. H. Sanders, *Clusters of galaxies with modified Newtonian dynamics*, MNRAS 342, 901 (2003), arXiv:astro-ph/0212293. *Verified* "
        "(abstract): discrepancy three to four times smaller, not removed.",
        "D. Clowe et al., *A direct empirical proof of the existence of dark matter*, ApJ 648, L109 (2006), arXiv:astro-ph/0608407. "
        "*Verified* (abstract): 8σ offset.",
        "M. Milgrom, ApJ 270, 365 (1983): a0 ≈ cH0/2π; record verified in `sparc_rotation.md`.",
    ]
    for i, r in enumerate(refs, 1):
        w(f"{i}. {r}")
    w("")
    fails = [k for k in o["checks"] if not k["ok"]]
    if fails:
        w("## Failed checks")
        w("")
        for k in fails:
            w(f"- {k['label']}")
        w("")
    return "\n".join(L) + "\n"


BLUE, ORANGE, AQUA, YELLOW, MAGENTA = "#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e87ba4"   # categorical slots 1-5, fixed order
INK, MUTED, DATA = "#1f1f1f", "#555555", "#9a9a9a"
MSTYLE = {"rar": (BLUE, "-", "o"), "const": (ORANGE, "--", "s"), "brown": (AQUA, "-.", "^"), "simple": (YELLOW, ":", "D")}


def figures(S, o, fit, per, Q, Pp, g5, null, PRO, TA, a_r1, B0, okb):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    plt.rcParams.update({"pdf.fonttype": 42, "font.size": 9, "axes.labelsize": 10, "legend.fontsize": 8, "axes.linewidth": 0.8,
                         "xtick.direction": "in", "ytick.direction": "in", "xtick.top": True, "ytick.right": True,
                         "savefig.bbox": "tight", "lines.linewidth": 1.6})
    FIGURES.mkdir(parents=True, exist_ok=True)
    meta = {"CreationDate": None, "ModDate": None, "Producer": None, "Creator": None}
    lab_gb = r"$g_{\rm bar}$ [m s$^{-2}$]"
    short = {"rar": r"RAR, $g_\dagger$", "const": r"constant $|\gamma_1|/2$", "brown": r"form B: $g_{\rm bar}+\sqrt{g_{\rm bar}a_{\rm acc}}$",
             "simple": r"form S: $\frac{g_{\rm bar}}{2}+\sqrt{\frac{g_{\rm bar}^2}{4}+g_{\rm bar}a_{\rm acc}}$"}

    # 1. the forms against the data
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11.0, 4.4))
    for k in ("rar", "const", "brown", "simple"):
        col, ls, mk = MSTYLE[k]
        res = S.y - MODELS[k]([fit[k][0]], S.g_bar, S.R)[0]
        bc, med, lo, hi = SR.binned_stats(S.x, res)
        if k == "rar":
            ax1.fill_between(10 ** bc, lo, hi, color=col, alpha=0.15, lw=0)
        ax1.plot(10 ** bc, med, ls=ls, marker=mk, ms=4, color=col, label=f"{short[k]} = {10 ** fit[k][0]:.2e}")
    ax1.axhline(0, color=MUTED, lw=0.8)
    ax1.set_xscale("log")
    ax1.set_ylim(-0.45, 0.45)
    ax1.set_xlabel(lab_gb)
    ax1.set_ylabel(r"$\log_{10}(g_{\rm obs}/g_{\rm model})$ [dex]")
    ax1.legend(loc="lower left", frameon=False, fontsize=7)
    ax1.text(0.02, 0.97, "(a) binned median residual, universal fits (L1); band: RAR 16-84% of points", transform=ax1.transAxes, va="top",
             fontsize=8, color=MUTED)
    dg = S.g_obs - S.g_bar
    pos = dg > 0
    ax2.scatter(S.g_bar[pos], dg[pos], s=3, color=DATA, alpha=0.35, lw=0, label=r"points with $g_{\rm obs}>g_{\rm bar}$")
    okp = np.isfinite(B0[:, 0]) & (B0[:, 1] > 0)
    ax2.plot(10 ** B0[okp, 0], B0[okp, 1], "s", ms=5, color=INK, label="binned median", zorder=5)
    gl = np.logspace(-12.6, -8.3, 300)
    for k in ("rar", "const", "brown", "simple"):
        col, ls, _ = MSTYLE[k]
        ax2.plot(gl, g_lin(k, gl, 10 ** fit[k][0]) - gl, ls=ls, color=col, label=short[k])
    ax2.axvspan(1e-13, 10 ** fit["rar"][0] / 10, color=MUTED, alpha=0.08, lw=0)
    rs = o["R1a"]["residual_slope"]
    ax2.text(0.02, 0.97, rf"(b) slope of $\log\Delta g$ in the shaded range: data {rs['data']:.2f}, RAR {rs['rar']:.2f}, "
             rf"S {rs['simple']:.2f}, B 0.50, constant 0", transform=ax2.transAxes, va="top", fontsize=8)
    ax2.set_xscale("log")
    ax2.set_yscale("log")
    ax2.set_xlim(10 ** -12.6, 10 ** -8.3)
    ax2.set_ylim(1e-13, 3e-9)
    ax2.set_xlabel(lab_gb)
    ax2.set_ylabel(r"$\Delta g=g_{\rm obs}-g_{\rm bar}$ [m s$^{-2}$]")
    ax2.legend(loc="lower right", frameon=False, fontsize=7)
    fig.tight_layout()
    fig.savefig(FIGURES / "remnant_forms.pdf", metadata=meta)
    plt.close(fig)

    # 2. natural scales
    b = o["R1b"]
    tt = np.array(b["profile_t"])
    fig, axs = plt.subplots(1, 2, figsize=(11.0, 4.2), sharey=True)
    for ax, k, tag in ((axs[0], "brown", "(a) form B"), (axs[1], "simple", "(b) form S")):
        col = MSTYLE[k][0]
        f_ = b["forms"][k]
        ax.plot(10 ** tt, np.array(b["profile"][k]) + 1, color=col, label=r"$\Delta(-2\ln L)+1$, universal fit (L1)")
        tb = math.log10(f_["best_native"])
        ax.axvspan(10 ** (tb - f_["sigma_tot_dex"]), 10 ** (tb + f_["sigma_tot_dex"]), color=col, alpha=0.2, lw=0,
                   label=rf"best $a_{{\rm acc}}$ $\pm\,\sigma_{{\rm tot}}$ ({f_['sigma_tot_dex']:.2f} dex)")
        order = sorted(b["candidates"].items(), key=lambda kv: kv[1])
        lo_grp = [kv for kv in order if kv[1] < 2e-10]
        hi_grp = [kv for kv in order if kv[1] >= 2e-10]
        levels = [4e5, 1.2e5, 3.5e4, 1e4, 3e3]
        for grp, ha in ((lo_grp, "left"), (hi_grp, "right")):
            for i, (name, val) in enumerate(grp):
                ls = "-" if "67.4" in name else ("--" if "73" in name else ":")
                ax.axvline(val, color=MUTED, lw=0.9, ls=ls)
                lab_ = name.replace(" (H0 = ", " (").replace(" (t0 = 13.8 Gyr)", "")
                ax.text(val * (1.03 if ha == "left" else 0.97), levels[i], lab_, fontsize=6, color=MUTED, ha=ha, va="center",
                        bbox=dict(facecolor="white", edgecolor="none", pad=0.5, alpha=0.8))
        le = f_["look_elsewhere"]
        ax.text(0.02, 0.03, f"{tag}: nearest scale {le['nearest_dex']:.3f} dex away;\n{le['n_within_2sigma_tot']} of 9 within 2$\\sigma$; "
                f"chance as close: {le['p_as_close_in_2dex_window']:.2f}", transform=ax.transAxes, va="bottom", fontsize=8)
        ax.set_xscale("log")
        ax.set_yscale("log")
        ax.set_xlim(10 ** tt[0], 10 ** tt[-1])
        ax.set_ylim(0.5, 1e6)
        ax.set_xlabel(r"$a_{\rm acc}$ [m s$^{-2}$]  (grey: candidate scales; solid $H_0$=67.4, dashed 73, dotted $c/t_0$)")
        ax.legend(loc="lower right", frameon=True, framealpha=0.9, edgecolor="none", fontsize=7)
    axs[0].set_ylabel(r"$-2\ln L - \min + 1$")
    fig.tight_layout()
    fig.savefig(FIGURES / "remnant_scales.pdf", metadata=meta)
    plt.close(fig)

    # 3. history
    tests = {(t["quantity"], t["proxy"]): t for t in o["R2"]["tests"]}
    qk = "log a_acc (B, per galaxy)"
    t5, s5 = per["brown"]["t"], per["brown"]["s_tot"]
    lM5 = np.log10(S.Mbar[g5])
    fig, axs = plt.subplots(2, 3, figsize=(12.0, 7.2), sharey=True)
    panels = [("log M_bar", lM5, r"$\log_{10} M_{\rm bar}$ [M$_\odot$]")] + [(pk, Pp[pk], {
        "Hubble type T": "Hubble type $T$", "gas fraction": r"gas fraction $1.33M_{\rm HI}/M_{\rm bar}$",
        "log SB_eff": r"$\log_{10}$ SB$_{\rm eff}$ [L$_\odot$ pc$^{-2}$]", "log R_disk": r"$\log_{10} R_{\rm disk}$ [kpc]",
        "log N_orb": r"$\log_{10} N_{\rm orb}=\log_{10}[t_0\,V_{\rm out}/(2\pi R_{\rm out})]$"}[pk]) for pk in Pp]
    for ax, (pk, xv, xl) in zip(axs.ravel(), panels):
        ax.errorbar(xv, t5, yerr=s5, fmt="o", ms=3, color=INK, ecolor=DATA, elinewidth=0.6, lw=0, zorder=3)
        ax.axhline(fit["brown"][0], color=AQUA, ls="-.", lw=1.2, label=r"universal $a_{\rm acc}$ (form B)")
        if pk == "log M_bar":
            e = o["R1c"]["brown"]
            txt = rf"Spearman $\rho$ = {e['spearman_logMbar'][0]:+.2f}, slope {e['slope_vs_logMbar']:+.2f}"
        else:
            t = tests[(qk, pk)]
            txt = (rf"$\rho$ = {t['rho']:+.2f} [{t['rho_boot_2.5_97.5'][0]:+.2f}, {t['rho_boot_2.5_97.5'][1]:+.2f}], $p_{{\rm Holm}}$ = {t['p_holm']:.2g}"
                   "\n" rf"null (universal RAR): [{t['null_rar_rho_2.5_97.5'][0]:+.2f}, {t['null_rar_rho_2.5_97.5'][1]:+.2f}]; "
                   f"predicted sign {'+' if o['R2']['predicted_sign'][pk] > 0 else '-'}")
        ax.text(0.02, 0.97, txt, transform=ax.transAxes, va="top", fontsize=7)
        ax.set_xlabel(xl)
        ax.set_ylim(-12.6, -8.4)
    for ax in axs[:, 0]:
        ax.set_ylabel(r"$\log_{10} a_{\rm acc}$ per galaxy, form B [m s$^{-2}$]")
    axs[0, 0].legend(loc="lower right", frameon=False, fontsize=7)
    fig.tight_layout()
    fig.savefig(FIGURES / "remnant_history.pdf", metadata=meta)
    plt.close(fig)

    # 4. halos and the joint fit
    pg = o["R3"]["per_galaxy"]
    n = np.array([p["n"] for p in pg])
    bic = {k: np.array([p[f"m2lnL_{k}"] for p in pg]) + kk * np.log(n) for k, kk in
           (("rar", 0), ("brown", 0), ("simple", 0), ("nfw_cm", 2), ("nfw_shmr", 2), ("burkert", 2))}
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11.0, 4.4))
    edges = np.arange(-80, 81, 5)
    for k, col, lab in (("nfw_cm", BLUE, "NFW + c-M prior"), ("nfw_shmr", ORANGE, "NFW + c-M + stellar-to-halo prior"),
                        ("burkert", AQUA, "Burkert"), ("simple", YELLOW, r"form S, universal $a_{\rm acc}$")):
        d = np.clip(bic[k] - bic["rar"], -79.9, 79.9)
        ax1.hist(d, bins=edges, histtype="step", color=col, lw=1.6, label=f"{lab}: better in {int(np.sum(d < 0))} of {len(d)}")
    ax1.axvline(0, color=MUTED, lw=0.8)
    ax1.set_xlabel(r"per-galaxy $\Delta$BIC against the universal RAR (clipped at $\pm$80)")
    ax1.set_ylabel("galaxies")
    ax1.legend(loc="upper left", frameon=False, fontsize=7)
    ax1.text(0.98, 0.97, "(a)", transform=ax1.transAxes, va="top", ha="right", fontsize=8, color=MUTED)
    F = o["R4"]["fits"]
    hname = {"nfw_cm": "NFW", "nfw_shmr": "NFW, cosmological", "burkert": "Burkert"}
    for hk, col in (("nfw_cm", BLUE), ("nfw_shmr", ORANGE), ("burkert", AQUA)):
        for sk, ls in (("sqrt", "-"), ("const", "--")):
            cur = np.array(F[f"{hk}+{sk}"]["dm2lnL_curve"])
            ax2.plot(10 ** TA, cur, color=col, ls=ls,
                     label=f"{hname[hk]} + " + (r"$\sqrt{g_{\rm bar}A}$" if sk == "sqrt" else "constant $A$"))
    ax2.axhline(2.71, color=INK, lw=0.8, ls=":")
    ax2.text(3e-10, 3.3, "95%\n(one-sided)", fontsize=7, color=INK, ha="right", va="bottom")
    for sk, ls in (("sqrt", "-"), ("const", "--")):
        ax2.axvline(a_r1[sk], color=MUTED, ls=ls, lw=1.0)
    ax2.text(a_r1["sqrt"] * 1.1, 0.15, "form B alone", fontsize=7, color=MUTED, rotation=90, va="bottom")
    ax2.text(a_r1["const"] * 0.9, 0.15, "constant alone", fontsize=7, color=MUTED, rotation=90, va="bottom", ha="right")
    ax2.set_xscale("log")
    ax2.set_yscale("symlog", linthresh=1.0)
    ax2.set_ylim(0, 3e4)
    ax2.set_xlim(10 ** TA[0], 10 ** TA[-1])
    ax2.set_xlabel(r"amplitude $A$ of the universal term [m s$^{-2}$]")
    ax2.set_ylabel(r"$\Delta(-2\ln L)$ against the best, summed over galaxies")
    ax2.legend(loc="upper left", frameon=False, fontsize=7)
    ax2.text(0.62, 0.97, "(b) halos refitted at every A", transform=ax2.transAxes, ha="center", va="top", fontsize=8, color=MUTED)
    fig.tight_layout()
    fig.savefig(FIGURES / "remnant_halos.pdf", metadata=meta)
    plt.close(fig)

    # 5. redshift
    z5 = o["R5"]
    zz = np.linspace(0, 3, 301)
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11.0, 4.4))
    gd0 = 10 ** fit["rar"][0]
    for (lw_, f), col in zip(LAWS.items(), (BLUE, ORANGE, AQUA, YELLOW)):
        r = np.array([f(z) for z in zz])
        ax1.plot(zz, r, color=col, label=lw_)
        ax2.plot(zz, -np.log10(r), color=col, label=f"{lw_}, deep regime")
        zc = zz[::10]
        ax2.plot(zc, [db_regime(f(z), 3.0, gd0) for z in zc], color=col, ls="--", lw=1.1)
    md = z5["musedark_ratio_vs_local"]
    ax1.errorbar([1.0], [md], yerr=[[z5["musedark_ratio_vs_local_err"]], [z5["musedark_ratio_vs_local_err"]]],
                 xerr=[[1.0 - MUSEDARK["z_lo"]], [MUSEDARK["z_hi"] - 1.0]], fmt="s", ms=6, color=INK, capsize=0,
                 label="MUSE-DARK III, $a_0(z\\approx1)$ / local 1.2e-10")
    ax1.plot([1.0], [z5["musedark_ratio_own_fit"]], "s", ms=6, mfc="none", mec=INK, label="MUSE-DARK III, own fit $a_0(z)=1.0+1.59z$")
    ax1.plot([2.0], [4.0], "x", ms=9, mew=2, color=INK, label="~4 $a_0$ at z ~ 2: 'all but excluded' (Milgrom 2017)")
    ax1.set_yscale("log")
    ax1.set_ylim(0.1, 10)
    ax1.yaxis.set_major_formatter(lambda v, _pos: f"{v:g}")
    ax1.yaxis.set_minor_formatter(lambda v, _pos: "")
    ax1.set_xlabel("redshift z")
    ax1.set_ylabel(r"$a_{\rm acc}(z)/a_{\rm acc}(0)$")
    ax1.legend(loc="lower left", frameon=True, framealpha=0.9, edgecolor="none", fontsize=7)
    ax1.text(0.98, 0.03, "(a)", transform=ax1.transAxes, ha="right", fontsize=8, color=MUTED)
    ax2.errorbar(UBLER17["z"], UBLER17["db"], yerr=UBLER17["db_err"], fmt="o", ms=6, color=INK, capsize=0,
                 label="Ubler et al. 2017 (bTFR, pressure-corrected; stat. errors)")
    ax2.plot(UBLER17["z"], UBLER17["db_no_pressure"], "o", ms=6, mfc="none", mec=INK, label="same, without pressure correction")
    ax2.axhline(0, color=MUTED, lw=0.8)
    ax2.plot([], [], color=MUTED, ls="--", lw=1.1, label=r"dashed: at $g_{\rm obs}=3g_\dagger$ (RAR shape)")
    ax2.set_xlabel("redshift z")
    ax2.set_ylabel(r"$\Delta\log M_{\rm bar}$ at fixed rotation speed [dex]")
    ax2.legend(loc="lower left", frameon=True, framealpha=0.9, edgecolor="none", fontsize=7, ncol=2)
    ax2.set_ylim(-1.45, 0.85)
    ax2.text(0.98, 0.97, "(b)", transform=ax2.transAxes, ha="right", va="top", fontsize=8, color=MUTED)
    fig.tight_layout()
    fig.savefig(FIGURES / "remnant_redshift.pdf", metadata=meta)
    plt.close(fig)


if __name__ == "__main__":
    main()
