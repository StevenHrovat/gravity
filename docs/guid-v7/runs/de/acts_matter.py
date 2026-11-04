# Steven 2026-11-04 17:49Z: "Since every quantum of Existence has to assert itself, the acts are equally spread out with the matter, though probably slightly less near
# very high gravities, because of time dilation. Since we assume dark matter to be PBHs, we can leave them out completely for the act generation ... but we have to
# account for them with the clumping."
# => act rate per comoving volume ∝ baryon number x (1 + Phi/c^2): constant in time (Phi/c^2 ~ 1e-6..1e-5 in haloes, BH/NS mass fraction tiny -> < 1e-4 effect, dropped).
# Clumping: haloes from TOTAL matter (PBH DM at asteroid mass clusters like CDM). If PBHs count as already clumped, the unclumped part is f_b(1-f_coll): same shape.
# Forms (trapping of evidence at the current time vs at emission):
#   U  : rho ∝ (1 - f_coll)                      [acts now that escape; = "unclumped alone" before]
#   I  : rho ∝ ∫ (1 - f_coll(t')) dt'            [evidence trapped at emission]
#   T  : rho ∝ t x (1 - f_coll(t))               [all evidence so far, trapped as regions clump now]
import sys, numpy as np
src=open('/mnt/project-files/gravity-v7/de/acts_datafit.py').read().split('res={}')[0]
exec(src)
tcos=np.array([quad(lambda x: dtdz(x), z, 1e4, limit=400)[0] for z in tz])  # cosmic time in 1/H0 units (Om 0.31)
new={}
for lM in [9,10,11,12,13]:
    s=sig(10.0**lM); un=np.array([1-fcoll(z,s) for z in tz])
    I=np.array([quad(lambda x: (1-fcoll(x,s))*dtdz(x), z, 1e3, limit=400)[0] for z in tz])
    for nm,r in [('U',un),('I',I),('T',tcos*un)]:
        new[f'{nm} M_esc=1e{lM}']=r/r[0]
tracers.update(new)
zz=[0,0.25,0.5,1,2]
L=fit('LCDM',[0.31,0.68,0.0224]).fun
print(f"LCDM chi2 {L:.2f}")
for k,r in new.items():
    i=np.argmax(r[tz<=3]); f=fit(k,[0.31,0.68,0.0224]); x=chi2(f.x,k)[1]
    print(f"{k:14s} rho(z=0,.25,.5,1,2) "+" ".join(f"{np.interp(q,tz,r):.2f}" for q in zz)+f"  peak z {tz[i]:.2f}  dchi2 {f.fun-L:+8.2f}  Om {f.x[0]:.4f} h {f.x[1]:.4f}")
