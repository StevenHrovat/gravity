"""Our predicted bubble-collision hum vs the public LIGO-Virgo O1+O2+O3 isotropic cross-correlation spectrum
(LVK, arXiv 2101.12130; data LIGO document G2001287 v5: C_O1_O2_O3.dat, columns f, C(f), sigma(f); Omega with H0 = 67.9 km/s/Mpc).
Template: envelope (Huber-Konstandin), v_w = 1, kappa = 1, alpha >> 1; beta/H from our late_patch scan (f_PBH = 1)."""
import numpy as np, sys
d = np.loadtxt(sys.argv[1] if len(sys.argv) > 1 else '/tmp/lvk/C_O1_O2_O3.dat')
f, C, s = d[:, 0], d[:, 1], d[:, 2]
ok = np.isfinite(C) & np.isfinite(s) & (s > 0); f, C, s = f[ok], C[ok], s[ok]
h2 = (67.9/100)**2
Msun, gs = 1.989e33, 106.75
def T_for_M(M): return 0.14*((Msun*(20/gs)**0.5)/M)**0.5
def fpeak(x, T): return 16.5e-6*(0.62/2.7)*x*(T/100.)*(gs/100)**(1/6)
def Omega(fr, x, T, amp=1.0):   # Omega (not h^2), using the LVK h
    r = fr/fpeak(x, T); S = 3.8*r**2.8/(1+2.8*r**3.8)
    return amp*1.67e-5*(1/x)**2*(100/gs)**(1/3)*0.077*S/h2
def betaH(M):   # our late_patch scan: f_PBH = 1 at 1e17/1e19/1e22 g -> 6.76/6.63/6.43 (interpolate in log M)
    return np.interp(np.log10(M), [17, 19, 22], [6.76, 6.63, 6.43])
print("M [g] | T [GeV] | beta/H | f_peak [Hz] | best-fit A/A_pred | 95% upper limit on A/A_pred | verdict")
for M in [1e15, 3e15, 1e16, 3e16, 1e17, 3e17, 1e18, 1e19]:
    x = betaH(M) if M >= 1e17 else 6.8; T = T_for_M(M)
    S = Omega(f, x, T)
    var = 1/np.sum(S**2/s**2); A = var*np.sum(C*S/s**2); sA = np.sqrt(var)
    ul = max(A, 0) + 1.645*sA
    print(f"{M:.0e} | {T:.2e} | {x:.2f} | {fpeak(x,T):.2e} | {A:+.3f} +- {sA:.3f} | {ul:.3f} | {'EXCLUDED' if ul < 1 else 'allowed'}")
