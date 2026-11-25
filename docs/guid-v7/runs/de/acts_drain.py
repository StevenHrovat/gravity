# Steven 2026-11-04 18:08Z: "The acts themselves, so the leftovers and verifications (neutrinos being one of them, along with, in our model another massive particle), would be
# the driver, so the supernova fit. Only uncaptured leftovers can drive the expansion. What get's trapped by clumping is the sources of the neutrinos, so less space has to
# stretch to drain all the energy."
# Drain law readings (acts = weak events in core-collapse SNe, rate ∝ SFR; leftover = SN neutrinos, energy redshifts = "drained by stretching"):
#  E0 : rho_DE ∝ E(t), comoving leftover energy still to drain, no source trapping (= "SN redshifted-E", run before)
#  Es : as E0 but sources inside clumps are trapped -> emission weighted by (1 - f_coll(>M, t_emit))
#  Ec : as E0 but sources trapped as regions clump NOW -> leftovers from now-clumped regions stop counting: E x (1 - f_coll(t)) (run before as +41)
#  P0/Ps : drain POWER H(t) E(t) (rate at which stretching removes leftover energy), without / with emission trapping
#  +CnuB: add the relic neutrino background's kinetic energy (masses 0.36, 8.7, 50 meV from the v7 balance) as further uncaptured leftovers
import sys, numpy as np
src=open('/mnt/project-files/gravity-v7/de/acts_datafit.py').read().split('res={}')[0]
exec(src)
Rsn=psi
def Ered(w):  # (1+z) * int_z^30 R(x) w(x)/(1+x) dt  : comoving energy, redshifting
    return np.array([(1+z)*quad(lambda x: Rsn(x)*w(x)/(1+x)*dtdz(x), z, 30, limit=200)[0] for z in tz])
new={}
E0=Ered(lambda x:1.0); new['E0 leftover energy']=E0/E0[0]
new['P0 drain power H*E']=E0*Hq(tz)/(E0[0]*Hq(0))
for lM in [10,11,12]:
    s=sig(10.0**lM)
    Es=Ered(lambda x: 1-fcoll(x,s)); new[f'Es emit-trapped 1e{lM}']=Es/Es[0]
    P=Es*Hq(tz); new[f'Ps power emit-trapped 1e{lM}']=P/P[0]
# relic neutrinos: kinetic energy density per species, p ~ 3.15 T_nu, T_nu0 = 1.676e-4 eV, n = 112 /cm^3 per species (nu + nubar)
Tn0=1.676e-4; ms=[0.36e-3,8.7e-3,50e-3]
def kin(z):
    p=3.15*Tn0*(1+z); return sum(112*(1+z)**3*(np.sqrt(p*p+m*m)-m) for m in ms)  # eV/cm^3, physical
# SN-neutrino leftover energy density today, physical: n ~3.0e-9 /cm^3 (acts_weak estimate) x mean redshifted energy
Esn_phys=lambda z: 3.0e-9*12e6*np.interp(z,tz,E0/E0[0])*(1+z)**3/ ( (quad(lambda x: Rsn(x)*dtdz(x),0,30)[0] / quad(lambda x: Rsn(x)/(1+x)*dtdz(x),0,30)[0]) )
print(f"today: CnuB kinetic {kin(0):.3g} eV/cm^3, SN-neutrino leftovers {Esn_phys(0):.3g} eV/cm^3 (physical)")
tot=np.array([Esn_phys(z)+kin(z) for z in tz])/(1+tz)**3  # comoving
new['E0 + CnuB kinetic']=tot/tot[0]
tracers.update(new)
L=fit('LCDM',[0.31,0.68,0.0224]).fun
print(f"LCDM chi2 {L:.2f}   (forms this run: {len(new)})")
zz=[0,0.25,0.5,1,2]
for k,r in new.items():
    i=np.argmax(r[tz<=3]); f=fit(k,[0.31,0.68,0.0224])
    print(f"{k:30s} rho(0,.25,.5,1,2) "+" ".join(f"{np.interp(q,tz,r):.2f}" for q in zz)+f"  peak z {tz[i]:.2f}  dchi2 {f.fun-L:+8.2f}  Om {f.x[0]:.4f}")
