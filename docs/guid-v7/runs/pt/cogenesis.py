"""Cogenesis check: one switch event -> PBH dark matter + matter surplus (2026-11-01).

After percolation the vacuum energy rho_V sits in the switch-sector field X (matter-like, mass m_X), a fraction beta_0 is
in black holes (matter-like, no accretion). X decays with rate Gamma, each decay leaves a lepton surplus eps (mirror
preference); sphalerons turn 28/79 of B-L into baryons. Radiation from the decays sets the entropy.
Claim to verify: Omega_PBH / Omega_b = (79/28) beta_0 m_X / (eps m_p), independent of Gamma (the dilution cancels).
Units: M_pl = 1 reduced; rho_V = 3 H*^2 with H* = 1; only ratios matter. g* = 106.75.
"""
import numpy as np
from scipy.integrate import solve_ivp

GS = 106.75; MP = 0.938

def run(gam, beta0, eps, mX_over_T):
    # variables vs N = ln a: rho_X a^3, rho_R a^4, rho_P a^3, nL a^3 (in units of rho_V)
    def rhs(N, y):
        X3, R4, P3, L3 = y
        a = np.exp(N)
        rhoX, rhoR, rhoP = X3 / a**3, R4 / a**4, P3 / a**3
        H = np.sqrt((rhoX + rhoR + rhoP) / 3.0)
        return [-gam / H * X3, gam / H * rhoX * a**4, 0.0, eps * gam / H * X3]   # nL counted in units of rho/m_X
    y0 = [1 - beta0, 1e-12, beta0, 0.0]
    Nend = np.log(1 / gam) * 0.75 + 12
    sol = solve_ivp(rhs, [0, Nend], y0, rtol=1e-9, atol=1e-30, method="LSODA")
    X3, R4, P3, L3 = sol.y[:, -1]
    a = np.exp(Nend)
    rhoR = R4 / a**4
    # rho_R = pi^2/30 gs T^4 ; s = 2 pi^2/45 gs T^3 -> s = (4/3) rho_R / T ; T in units where rho_V = 1: T = (30 rhoR/(pi^2 gs))^(1/4)
    T = (30 * rhoR / (np.pi**2 * GS)) ** 0.25
    s = 4 / 3 * rhoR / T
    # convert: nL [in rho_V/m_X units] ; T_V defined by rho_V = pi^2/30 gs T_V^4 -> T_V = (30/(pi^2 gs))^(1/4) in these units
    TV = (30 / (np.pi**2 * GS)) ** 0.25
    mX = mX_over_T * TV
    nL = L3 / a**3 / mX
    YB = 28 / 79 * nL / s
    rhoP_s = P3 / a**3 / s
    # rho_P/s is in units where rho_V=1; Y_B dimensionless; m_p in the same units: m_p = MP/(T_V in GeV) * TV ; ratio independent of T_V scale if m_X fixed in GeV
    return rhoP_s, YB, T / TV

if __name__ == "__main__":
    print(__doc__)
    TV_GeV = 3.2e6; mX_GeV = 3.2e6
    print(f"T_V = {TV_GeV:.1e} GeV, m_X = {mX_GeV:.1e} GeV")
    print(f"{'Gamma/H*':>9} {'beta0':>8} {'eps':>8} {'T_reh/T_V':>10} {'Y_B':>9} {'Omega_P/Omega_b':>15} {'formula':>9}")
    for gam in (3e-3, 1e-3, 3e-4, 1e-4):
        for beta0, eps in ((1e-14, 5e-9), (1e-14, 1e-8)):
            rPs, YB, tr = run(gam, beta0, eps, mX_GeV / TV_GeV)
            TVu = (30 / (np.pi**2 * GS)) ** 0.25
            mp_units = MP / TV_GeV * TVu
            ratio = rPs / (mp_units * YB)
            formula = 79 / 28 * beta0 * mX_GeV / (eps * MP)
            print(f"{gam:9.0e} {beta0:8.0e} {eps:8.0e} {tr:10.3e} {YB:9.2e} {ratio:15.3f} {formula:9.3f}")
    print("\nObserved: Y_B = 8.7e-11, Omega_DM/Omega_b = 5.36. With m_X = T_V the event needs eps / beta0 = (79/28) m_X/(5.36 m_p).")
    for TV in (1e5, 1e6, 3.2e6, 1e7, 3.2e7):
        print(f"  m_X = {TV:.1e} GeV: eps/beta0 = {79/28*TV/(5.36*MP):.2e}")
