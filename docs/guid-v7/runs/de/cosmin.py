# CosMIn check (Padmanabhan & Padmanabhan 2013, arXiv 1302.3226; formula NOT read from source - derived here):
# number of modes crossing the Hubble radius per log k inside a Hubble sphere: dN = (4pi/3)/(6 pi^2) * 3 dln(aH) = (2/(3 pi)) dln(aH)
# N_c = (2/(3pi)) ln[(aH)_end_of_inflation / (aH)_min_late]; postulate N_c = 4 pi  <=>  ln ratio = 6 pi^2 = 59.22
# Scaling check: instant reheating -> rho_L ~ rho_inf^(3/2) rho_eq^(-1/2) e^(-36 pi^2) (matches the published form from memory, prefactor aside).
import numpy as np, math
Mp=2.435e18      # reduced Planck mass GeV
T0=2.348e-13     # CMB temperature GeV (2.725 K)
h=0.677; H0=2.133e-42*h  # GeV
Om=0.311; OL=0.689; Or=9.1e-5
def rho_rad(T,g): return math.pi**2/30*g*T**4
# late part: (aH) at T=1 MeV and (aH)_min from LCDM
g1=10.75; gs1=10.75; gs0=3.91
T1=1e-3
a1=(gs0/gs1)**(1/3)*T0/T1
H1=math.sqrt(rho_rad(T1,g1)/3)/Mp
a=np.logspace(-2,1,200001); aH=a*H0*np.sqrt(Om*a**-3+OL+Or*a**-4)
i=np.argmin(aH); aHmin=aH[i]
print(f"(aH)_min at a={a[i]:.3f} (z={1/a[i]-1:.2f}); ln[(aH)_1MeV/(aH)_min] = {math.log(a1*H1/aHmin):.3f}")
L_late=math.log(a1*H1/aHmin)
gHigh=106.75
def lnratio(rho_end, Treh1, TV=None, G=None, Nsc=0.0, gD=110.0):
    """ln[(aH)_end/(aH)_min]; eras: inflaton-matter rho_end->Treh1, radiation Treh1->(TV: vacuum Nsc e-folds, X-matter until Gamma, radiation at Treh2)->1 MeV, LCDM."""
    L=L_late
    # radiation from Treh_low up to ... handle with g* factors: aH ∝ g^(1/2) gs^(-1/3) T
    fac=lambda T,g: math.log(g**0.5*g**(-1/3)*T)
    if TV is None:
        L+= fac(Treh1,gHigh)-fac(T1,g1)
    else:
        Treh2=0.64*math.sqrt(G)*TV
        L+= fac(Treh2,gHigh)-fac(T1,g1)               # radiation 1 MeV -> Treh2
        rv=rho_rad(TV,gD); r2=rho_rad(Treh2,gHigh)
        L+= (1/6)*math.log(rv/r2)                      # X-matter era (rho falls by (G)^2 approx)
        L-= Nsc                                        # supercooled vacuum era: aH grows by e^Nsc going forward
        L+= fac(Treh1,gHigh)-fac(TV,gHigh)             # radiation TV -> Treh1
    L+= (1/6)*math.log(rho_end/rho_rad(Treh1,gHigh))   # inflaton oscillation
    return L
target=6*math.pi**2
V0=0.75*Mp**2*(3.1e13)**2; rho_end=0.43*V0
print(f"Starobinsky V0^(1/4)={V0**0.25:.2e} GeV, rho_end^(1/4)={rho_end**0.25:.2e} GeV; target ln ratio 6pi^2 = {target:.2f}")
def report(label,L):
    Nc=2/(3*math.pi)*L
    pred=math.exp(-6*(target-L))  # rho_L,pred / rho_L,obs
    print(f"{label:62s} ln={L:6.2f}  N_c={Nc:6.3f} (4pi={4*math.pi:.3f})  rho_L(pred)/obs = 10^{math.log10(pred):+.1f}")
report("instant reheating at rho_end (Padmanabhan's case)", lnratio(rho_end, (rho_end/(math.pi**2/30*gHigh))**0.25))
report("Starobinsky + T_reh 2.3e9 GeV, no switch", lnratio(rho_end,2.3e9))
for TV in [1e5,3e6,3e7]:
    for G in [3e-3,3e-4]:
        for Nsc in [0,5,10]:
            report(f"+ switch T_V={TV:.0e}, Gamma/H*={G:.0e}, supercool {Nsc} e-folds", lnratio(rho_end,2.3e9,TV,G,Nsc))
