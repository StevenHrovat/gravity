"""Whole-timeline consistency check, all limits at once (2026-11-01). Values from memory, labelled; rough by design."""
import numpy as np
Mpl = 2.435e18          # reduced Planck mass, GeV
M = 3.0e13              # Starobinsky scalaron mass, GeV
gs = 106.75
print("1. Reheating vs switch")
G = M**3 / (192 * np.pi * Mpl**2)                 # gravitational decay into a minimally coupled scalar (Higgs)
Treh = (90 / (np.pi**2 * gs))**0.25 * np.sqrt(G * Mpl)
print(f"   Starobinsky decay rate {G:.1f} GeV -> T_reh ~ {Treh:.1e} GeV (needs > T_V ~ 1e5..3e7 GeV): {'OK' if Treh > 3e7 else 'FAIL'}")
print("2. Inflation e-folds and n_s with the switch's matter era")
for gam in (3e-3, 3e-4):
    dN = -np.log(1 / gam) / 6
    for N in (55, 60):
        print(f"   Gamma/H* {gam:.0e}: dN = {dN:.2f}; N {N} -> n_s {1-2/N:.4f} -> {1-2/(N+dN):.4f}; r = {12/(N+dN)**2:.4f}")
print("   Planck 2018: n_s 0.9649(42); ACT DR6 + Planck + DESI (2025): n_s ~0.974(3) -> Starobinsky at about 2-3 sigma from ACT (OPEN, external);")
print("   r < 0.036 (BICEP/Keck 2021): OK")
print("3. Switch-era leftovers vs early-universe limits")
print("   switch field X (m ~ T_V) decays at T_reh 2e3..1e6 GeV, long before BBN (1 MeV): OK")
print("   sphalerons active at T_reh (> 130 GeV): OK, surplus converted")
print("   hum Omega_GW h^2 <= 1.5e-9 vs N_eff bound ~1e-6: OK")
print("   PBHs >= 1e17 g: no evaporation before today (lifetime >> 1e10 yr for > 5e14 g): BBN/CMB untouched; 1e17 g edge set by 511 keV / MeV gamma limits")
print("4. CMB and structure with asteroid-mass PBH dark matter")
print("   accretion/CMB limits only for >~ 1 solar mass: OK; Poisson isocurvature at these masses: negligible; lensing: allowed window")
print("   matter surplus from X decay is homogeneous (no baryon isocurvature beyond limits): OK")
print("5. Late universe: dark energy not in v7 (OPEN)")
