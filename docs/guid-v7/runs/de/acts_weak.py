# Steven 2026-11-04 17:56Z: acts = matter changing state; photons and gluons leave nothing behind but their effect on the recipient -> acts = WEAK interactions.
# Weak-act sources (late universe): (1) core-collapse supernovae (neutronisation e+p->n+nu ~1e57 per SN, plus thermal weak pair neutrinos ~1.5e58), prompt -> rate ∝ SFR;
# (2) hydrogen fusion in stars (2 p->n conversions per He-4) -> rate ∝ stellar luminosity density = SFR convolved with SSP light curve l(tau) ∝ (tau+3 Myr)^-0.85 (rough, Tinsley-type);
# (3) early universe: weak freeze-out ~1 s, then free neutron decay to BBN (~1.8% of baryons) -> a constant baseline B if counted.
# Budget per Msun of stars formed (orders of magnitude, from memory): SN events ~0.01 x 1.6e58 = 1.6e56 (all weak events) or 0.01 x 8e56 = 8e54 (p->n only);
# fusion conversions ~5.9e56 x ~5% burned over a Hubble time = 3e55. Per baryon: stars ~1.5e-3 conversions vs BBN neutron decay ~1.8e-2 (12x more).
import sys, numpy as np
src=open('/mnt/project-files/gravity-v7/de/acts_datafit.py').read().split('res={}')[0]
exec(src)
# cosmic time grid (units 1/H0) for convolution
zc=np.concatenate([np.linspace(0,3,121),np.linspace(3.05,30,200)])
tc=np.array([quad(lambda x: dtdz(x), z, 1e4, limit=400)[0] for z in zc])
H0Gyr=977.8/(100*0.677)  # 1/H0 in Gyr
order=np.argsort(tc); Tt=tc[order]; Z=zc[order]; S=psi(Z)
def lum(i):
    tau=(Tt[i]-Tt[:i+1])*H0Gyr
    return np.trapezoid(S[:i+1]*(tau+0.003)**-0.85, Tt[:i+1])
Lf=np.array([lum(i) for i in range(len(Tt))])
Rfus=lambda z: np.interp(z,Z[::-1],Lf[::-1])
Rsn=psi
def cumR(R): return np.array([quad(lambda x: R(x)*dtdz(x), z, 30, limit=200)[0] for z in tz])
def Ered(R):  # comoving energy of escaped neutrinos, redshifting: E(z) = (1+z) * int_z^30 R(x)/(1+x) dt
    return np.array([(1+z)*quad(lambda x: R(x)/(1+x)*dtdz(x), z, 30, limit=200)[0] for z in tz])
cS,cF=cumR(Rsn),cumR(Rfus); eS,eF=Ered(Rsn),Ered(Rfus)
# conversion-weighted mix: fusion 3e55 : SN 8e54 per Msun at the end of a Hubble time -> weights on the cumulative counts today
mix=cF/cF[0]*0.79+cS/cS[0]*0.21
new={}
for lM in [9,10,11]:
    un=np.array([1-fcoll(z,sig(10.0**lM)) for z in tz])
    for nm,cc in [('fusion',cF),('SN',cS),('mix(conv)',mix)]:
        r=cc*un; new[f'{nm} x unclumped 1e{lM}']=r/r[0]
new['fusion redshifted-E']=eF/eF[0]; new['SN redshifted-E']=eS/eS[0]
for lM in [10]:
    un=np.array([1-fcoll(z,sig(10.0**lM)) for z in tz])
    r=eS*un; new[f'SN redshifted-E x unclumped 1e{lM}']=r/r[0]
base=cS*np.array([1-fcoll(z,sig(1e10)) for z in tz]); base=base/base[0]
for B in [0.5,0.9,12/13]:
    new[f'BBN baseline B={B:.2f} + SN 1e10']=B+(1-B)*base
tracers.update(new)
L=fit('LCDM',[0.31,0.68,0.0224]).fun
print(f"LCDM chi2 {L:.2f}   (forms this run: {len(new)})")
zz=[0,0.25,0.5,1,2]
for k,r in new.items():
    i=np.argmax(r[tz<=3]); f=fit(k,[0.31,0.68,0.0224])
    print(f"{k:34s} rho(0,.25,.5,1,2) "+" ".join(f"{np.interp(q,tz,r):.2f}" for q in zz)+f"  peak z {tz[i]:.2f}  dchi2 {f.fun-L:+7.2f}  Om {f.x[0]:.4f}")
print("fusion rate / SFR shape (z: 0,.5,1,2,3):"," ".join(f"{Rfus(q)/Rfus(0):.2f}/{psi(q)/psi(0):.2f}" for q in [0,0.5,1,2,3]))
