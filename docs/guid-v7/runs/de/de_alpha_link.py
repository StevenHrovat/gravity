# Dark energy check 1: can GUID's information scalar (the alpha field, Bekenstein reading) also be the dark energy?
# Inputs from memory (flagged): H0 = 67.7 km/s/Mpc, Omega_DE = 0.69, rho_Lambda^(1/4) ~ 2.3 meV,
# atomic-clock alpha drift (Lange et al. 2021, PRL 126 011102): (1.0 +- 1.1)e-18 per year,
# quasar many-multiplet bounds ~ |dalpha/alpha| < ~1e-6 at z ~ 1-3 (order of magnitude), Oklo |dalpha/alpha| < ~1e-7 at z ~ 0.16.
import math
H0_kms=67.7; Mpc=3.0857e19; yr=3.156e7
H0=H0_kms/Mpc*yr          # per year
OmDE=0.69
print(f"H0 = {H0:.3e} /yr")
# Quintessence slow roll today: (phi_dot/M_Pl)^2 = 3 (1+w) Omega_DE H0^2
clock_2sig=1.0e-18+2*1.1e-18
for w in [-0.99,-0.95,-0.9,-0.8,-0.75]:
    phidot=math.sqrt(3*(1+w)*OmDE)*H0
    zeta=clock_2sig/phidot
    # field excursion since z~1 (crude: ~ phidot * 8 Gyr)
    dphi=phidot*8e9
    zeta_q=1e-6/dphi
    print(f"w0={w:+.2f}: phi_dot/M_Pl={phidot:.2e}/yr  clock -> zeta<{zeta:.1e}  quasar(z~1) -> zeta<{zeta_q:.1e}  (field moved {dphi:.2f} M_Pl since z~1)")
# Natural coupling for alpha = alpha0 exp(2 zeta phi/M_Pl)-type: zeta ~ O(1); BSBM-type in Bekenstein units ~ O(1e-4..1)
rho=(2.3e-3)**4  # eV^4
print(f"rho_Lambda ~ ({2.3e-3*1e3:.1f} meV)^4 = {rho:.1e} eV^4; Planck^4/rho = {(1.22e28)**4/rho:.1e}; (100 GeV)^4/rho = {(1e11)**4/rho:.1e}")
# neutrino scale comparison (round 1 balance masses)
m=[0.36,8.66,50.1]
print("neutrino masses meV:",m,"; rho_L^(1/4) = 2.3 meV; sqrt(m1 m3) =",round(math.sqrt(m[0]*m[2]),2),"meV (numerology, no look-elsewhere control)")
