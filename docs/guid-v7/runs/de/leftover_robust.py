# Leftover law (Steven 18:08Z-18:16Z): rho_DE ∝ [count of SN weak leftovers so far] x [unclumped share now]; relic nus = uniform bath, no drive. Amount = one input.
# Robustness: (1) SFR history Madau-Fragos 2017 (psi ∝ (1+z)^2.6/(1+((1+z)/3.2)^6.2), from memory) vs Madau-Dickinson 2014;
# (2) held-out: fit on BAO+CMB only, then score the supernovae; fit on SN+CMB only, then score BAO.
import sys, numpy as np
src=open('/mnt/project-files/gravity-v7/de/acts_datafit.py').read().split('res={}')[0]
exec(src)
psiMF=lambda z:(1+z)**2.6/(1+((1+z)/3.2)**6.2)
cMF=np.array([quad(lambda x: psiMF(x)*dtdz(x),z,30,limit=200)[0] for z in tz])
for lM in [9,10,11]:
    un=np.array([1-fcoll(z,sig(10.0**lM)) for z in tz]); r=cMF*un; tracers[f'MF17 1e{lM}']=r/r[0]
L=fit('LCDM',[0.31,0.68,0.0224]).fun
print(f"LCDM {L:.2f}")
for k in ['acts=SFR M_esc=1e9','acts=SFR M_esc=1e10','acts=SFR M_esc=1e11','MF17 1e9','MF17 1e10','MF17 1e11']:
    f=fit(k,[0.31,0.68,0.0224]); r=tracers[k]; i=np.argmax(r[tz<=3])
    print(f"{k:22s} dchi2 {f.fun-L:+7.2f}  peak z {tz[i]:.2f}  bump {100*(r[i]-1):.1f}%  rho(z=2) {np.interp(2,tz,r):.2f}")
# held-out
def fitpart(model,x0,parts):
    def f(p):
        v=chi2(p,model)
        if np.isscalar(v): return 1e9
        return sum(v[1][j] for j in parts)
    best=None
    for dx in [0,0.01,-0.01]:
        r=minimize(f,np.array(x0)+dx*np.array([1,0.5,0.01]+[1]*(len(x0)-3)),method='Nelder-Mead',options={'xatol':1e-6,'fatol':1e-4,'maxiter':6000,'maxfev':12000})
        if best is None or r.fun<best.fun: best=r
    return best
print("\nheld-out (parts: 0 BAO, 1 SN, 2 CMB). Score of the part NOT used in the fit:")
for train,test,lab in [((0,2),1,'fit BAO+CMB -> score SN'),((1,2),0,'fit SN+CMB -> score BAO')]:
    out=[]
    for k,x0 in [('LCDM',[0.31,0.68,0.0224]),('CPL',[0.31,0.68,0.0224,-0.85,-0.6]),('acts=SFR M_esc=1e10',[0.31,0.68,0.0224]),('MF17 1e10',[0.31,0.68,0.0224])]:
        r=fitpart(k,x0,train); v=chi2(r.x,k)[1]; out.append((k,v[test],r.x))
    base=out[0][1]
    print(lab+": "+" | ".join(f"{k} {v-base:+.2f}" + (f" (w0 {x[3]:.2f} wa {x[4]:.2f})" if k=='CPL' else "") for k,v,x in out))
