# Structure growth under Steven's acts-slowed-by-clumping law vs LCDM and CPL, using CAMB 2.0.5 (DarkEnergyPPF, w(a) table; the acts term is treated as smooth, like Lambda).
# Background parameters: best fits from acts_datafit.py (argv[1] pantheon|des). Primordial: Planck 2018 As 2.099e-9 (ln 10^10 As 3.044), ns 0.9649, tau 0.0544, sum m_nu 0.06.
import sys, numpy as np, camb
src=open('/mnt/project-files/gravity-v7/de/acts_datafit.py').read().split('res={}')[0]
exec(src)
zs_out=[0.0,0.067,0.15,0.38,0.51,0.70,0.85,1.48]
def wtable(model,p):
    a=np.geomspace(1e-4,1,400); z=1/a-1
    if model=='LCDM': return None
    if model=='CPL': return a, p[0]+p[1]*(1-a)
    lr=np.log(np.maximum(fDE(model,z,p),1e-30))
    w=-1-np.gradient(lr,np.log(a))/3
    return a, np.clip(w,-3,1.0)   # high-z cap: DE density there is < 1e-3 of today, effect negligible
def run(model,x0):
    r=fit(model,x0); Om,h,ob=r.x[:3]; ex=r.x[3:]
    pars=camb.CAMBparams()
    oc=Om*h*h-ob-0.06/93.14
    pars.set_cosmology(H0=100*h,ombh2=ob,omch2=oc,mnu=0.06,tau=0.0544)
    pars.InitPower.set_params(As=2.099e-9,ns=0.9649)
    wt=wtable(model,ex)
    if wt is not None:
        pars.DarkEnergy=camb.dark_energy.DarkEnergyPPF(); pars.DarkEnergy.set_w_a_table(wt[0],wt[1])
    pars.set_matter_power(redshifts=zs_out[::-1],kmax=2.0)
    res=camb.get_results(pars)
    s8=res.get_sigma8()[::-1]; fs8=res.get_fsigma8()[::-1]
    # check CAMB background vs our H(z) at z=0.5
    return r, s8, fs8, res
SN=sys.argv[1] if len(sys.argv)>1 else 'pantheon'
print('SN set', SN)
print(f"{'model':24s}{'chi2':>9s}{'Om':>7s}{'h':>7s}{'sigma8':>8s}{'S8':>7s}   fsigma8 at z = "+" ".join(f"{z:.3f}" for z in zs_out[1:]))
for model,x0 in [('LCDM',[0.31,0.68,0.0224]),('CPL',[0.31,0.68,0.0224,-0.85,-0.6]),('acts=SFR M_esc=1e9',[0.31,0.68,0.0224]),('acts=SFR M_esc=1e10',[0.31,0.68,0.0224]),('acts=SFR M_esc=1e11',[0.31,0.68,0.0224]),('acts=collapse M_esc=1e13',[0.31,0.68,0.0224])]:
    r,s8,fs8,res=run(model,x0)
    Om=r.x[0]
    Hc=res.hubble_parameter(0.5); Hm=100*r.x[1]*np.sqrt(Om*1.5**3+(1-Om)*fDE(model,np.array([0.5]),r.x[3:])[0])
    print(f"{model:24s}{r.fun:9.2f}{Om:7.4f}{r.x[1]:7.4f}{s8[0]:8.4f}{s8[0]*np.sqrt(Om/0.3):7.4f}   "+" ".join(f"{v:.4f}" for v in fs8[1:])+f"   [H(0.5) CAMB/ours {Hc/Hm:.4f}]")
