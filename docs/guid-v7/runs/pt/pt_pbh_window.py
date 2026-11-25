# Supercooled first-order transition -> asteroid-mass PBHs: what the switch needs.
# Formulas: Gouttenoire & Volansky 2305.04942 (P_coll fit, f_PBH, M_PBH; flat-gauge delta, optimistic),
# GW envelope template Huber & Konstandin 0806.1828 / Caprini et al. 1512.06239 (v_w=1, alpha>>1, kappa->1).
import math
Msun=1.989e33; gs=106.75
a,b,c=1.024,0.6921,0.8831
def M_pbh(T): return Msun*(20/gs)**0.5*(0.14/T)**2          # grams, T in GeV
def T_for_M(M): return 0.14*((Msun*(20/gs)**0.5)/M)**0.5
def Pcoll(x,dc): return math.exp(-a*x**b*(1+dc)**(c*x))
def fpbh(x,dc,T): return Pcoll(x,dc)/6.0e-12*(T/500.)
def solve_x(dc,T):
    lo,hi=2.0,12.0
    for _ in range(200):
        m=0.5*(lo+hi)
        if fpbh(m,dc,T)>1: lo=m
        else: hi=m
    return 0.5*(lo+hi)
def fpeak(x,T): return 16.5e-6*(0.62/2.7)*x*(T/100.)*(gs/100)**(1/6)
def Om(f,x,T):
    fp=fpeak(x,T); r=f/fp
    S=3.8*r**2.8/(1+2.8*r**3.8)
    return 1.67e-5*(1/x)**2*(100/gs)**(1/3)*0.077*S
print("PBH mass <-> transition temperature (reheat T after the switch)")
for M in (1e17,1e18,1e19,1e20,1e21,1e22):
    print(f"  M={M:.0e} g  ->  T={T_for_M(M):.2e} GeV")
print("\nbeta/H needed for f_PBH=1 (P_coll fit valid for beta/H 3..8, delta_c 0.4..2/3)")
for M in (1e17,1e19,1e22):
    T=T_for_M(M)
    row=[]
    for dc in (0.4,0.5,2/3):
        x=solve_x(dc,T); row.append(f"dc={dc:.2f}: {x:.2f}")
    print(f"  M={M:.0e} g T={T:.1e}: P_coll needed={6e-12*500/T:.1e};  "+"; ".join(row))
T=T_for_M(1e19); x=solve_x(0.5,T)
print(f"\nSensitivity at M=1e19 g, dc=0.5: beta/H={x:.3f}")
for dx in (-0.2,-0.1,-0.05,0.05,0.1,0.2):
    print(f"  beta/H {x+dx:.3f}: f_PBH = {fpbh(x+dx,0.5,T):.2e}")
print("\nGW background (envelope template, peak Omega h^2 and value at detector bands)")
for M in (1e17,1e19,1e22):
    T=T_for_M(M); x=solve_x(0.5,T); fp=fpeak(x,T)
    pk=Om(fp,x,T)
    print(f"  M={M:.0e} g T={T:.1e} beta/H={x:.2f}: f_peak={fp:.2e} Hz, Omega_peak h2={pk:.1e}; "
          f"at 3 mHz (LISA) {Om(3e-3,x,T):.1e}; at 0.3 Hz (DECIGO) {Om(0.3,x,T):.1e}; at 10 Hz (ET) {Om(10,x,T):.1e}; at 25 Hz (LIGO) {Om(25,x,T):.1e}")
print("Reference reach (round numbers): LIGO-Virgo O3 limit ~6e-9 near 25 Hz (2101.12130); LISA ~1e-12..1e-13 at mHz; ET ~1e-12 near 10 Hz; DECIGO/BBO ~1e-15..1e-16 near 0.1-1 Hz.")
