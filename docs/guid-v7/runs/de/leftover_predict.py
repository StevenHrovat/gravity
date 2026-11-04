# Predictions of the leftover law (MD14 SFR, M_esc 1e10; MF17 as check) vs LCDM and CPL, each at its joint best fit (argv[1] pantheon|des).
# Outputs: table of w(z), rho_DE/rho_DE0, H/H_LCDM-1, D_M/r_d vs LCDM, f sigma8 (CAMB 2.0.5, As/ns Planck), S8; figure leftover_predict.png.
import sys, numpy as np, camb
src=open('/mnt/project-files/gravity-v7/de/acts_datafit.py').read().split('res={}')[0]
exec(src)
psiMF=lambda z:(1+z)**2.6/(1+((1+z)/3.2)**6.2)
cMF=np.array([quad(lambda x: psiMF(x)*dtdz(x),z,30,limit=200)[0] for z in tz])
un=np.array([1-fcoll(z,sig(1e10)) for z in tz]); r=cMF*un; tracers['leftover MF17 1e10']=r/r[0]
models=[('LCDM',[0.31,0.68,0.0224]),('CPL',[0.31,0.68,0.0224,-0.85,-0.6]),('acts=SFR M_esc=1e10',[0.31,0.68,0.0224]),('leftover MF17 1e10',[0.31,0.68,0.0224])]
zq=np.array([0,0.3,0.51,0.71,0.93,1.32,1.48,2.0,2.33,3.0])
res={}
for k,x0 in models:
    f=fit(k,x0); Om,h,ob=f.x[:3]; ex=f.x[3:]
    Or=og*(1+0.2271*Neff)/h**2; ODE=1-Om-Or
    E=np.sqrt(Or*(1+zgrid)**4+Om*(1+zgrid)**3+ODE*fDE(k,zgrid,ex))
    DC=np.concatenate([[0],np.cumsum(0.5*(1/E[1:]+1/E[:-1])*np.diff(zgrid))])*c/(100*h)
    ocb=Om*h*h-onu; rd=55.154*np.exp(-72.3*(onu+0.0006)**2)/(ocb**0.25351*ob**0.12807)
    a=np.geomspace(1e-4,1,600); zz=1/a-1; lr=np.log(np.maximum(fDE(k,zz,ex),1e-30)); w=-1-np.gradient(lr,np.log(a))/3
    pars=camb.CAMBparams(); pars.set_cosmology(H0=100*h,ombh2=ob,omch2=Om*h*h-ob-onu,mnu=0.06,tau=0.0544); pars.InitPower.set_params(As=2.099e-9,ns=0.9649)
    if k!='LCDM':
        pars.DarkEnergy=camb.dark_energy.DarkEnergyPPF(); pars.DarkEnergy.set_w_a_table(a,np.clip(w,-3,1))
    pars.set_matter_power(redshifts=list(zq[::-1]),kmax=2.0); cr=camb.get_results(pars)
    fs8=cr.get_fsigma8()[::-1]; s8=cr.get_sigma8()[::-1][0]
    res[k]=dict(chi=f.fun,Om=Om,h=h,H=lambda z,E=E,h=h: 100*h*np.interp(z,zgrid,E),DM=lambda z,DC=DC,rd=rd: np.interp(z,zgrid,DC)/rd,
                rho=lambda z,k=k,ex=ex: fDE(k,np.atleast_1d(z),ex),w=lambda z,a=a,w=w: np.interp(1/(1+np.atleast_1d(z)),a,w),fs8=fs8,S8=s8*np.sqrt(Om/0.3))
L=res['LCDM']
print("SN set",sys.argv[1] if len(sys.argv)>1 else 'pantheon')
for k in res:
    R=res[k]; print(f"\n{k}: chi2 {R['chi']:.2f} (d {R['chi']-L['chi']:+.2f})  Om {R['Om']:.4f} h {R['h']:.4f}  S8 {R['S8']:.4f}")
    print("   z     w      rho/rho0  H/H_LCDM-1[%]  DM/rd vs LCDM[%]  fsig8  fsig8 vs LCDM[%]")
    for i,z in enumerate(zq):
        print(f"  {z:4.2f} {R['w'](z)[0]:7.3f} {R['rho'](z)[0]:8.3f} {100*(R['H'](z)/L['H'](z)-1):10.2f} {100*(R['DM'](z)/L['DM'](z)-1) if z>0 else 0:14.2f} {R['fs8'][i]:9.4f} {100*(R['fs8'][i]/L['fs8'][i]-1):10.2f}")
# leftover vs CPL directly
A,B=res['acts=SFR M_esc=1e10'],res['CPL']
print("\nleftover (MD14 1e10) minus DESI-type CPL, both at their own best fit:")
for z in [0.5,1.0,1.5,2.0,2.33,3.0]:
    print(f"  z {z}: H {100*(A['H'](z)/B['H'](z)-1):+.2f}%  DM/rd {100*(A['DM'](z)/B['DM'](z)-1):+.2f}%  rho_DE {A['rho'](z)[0]:.2f} vs {B['rho'](z)[0]:.2f}")
# figure
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
zp=np.linspace(0,3,301)
plt.rcParams.update({'font.size':11,'axes.edgecolor':'#52514e','axes.labelcolor':'#0b0b0b','xtick.color':'#52514e','ytick.color':'#52514e'})
fig,ax=plt.subplots(1,3,figsize=(15,4.6),facecolor='#fcfcfb')
for a_ in ax: a_.set_facecolor('#fcfcfb'); a_.grid(color='#e6e5e0',lw=0.8); [a_.spines[s].set_visible(False) for s in ['top','right']]
ser=[('LCDM','Standard model (constant)','#8a8984','--'),('CPL',"DESI-type fit (w0, wa)",'#2a78d6','-'),('acts=SFR M_esc=1e10','Leftover law (no shape knob)','#eb6834','-')]
for k,lab,col,ls in ser:
    R=res[k]
    ax[0].plot(zp,R['rho'](zp),color=col,ls=ls,lw=2,label=lab)
    ax[1].plot(zp,R['w'](zp),color=col,ls=ls,lw=2,label=lab)
    ax[2].plot(zp,100*(R['H'](zp)/L['H'](zp)-1),color=col,ls=ls,lw=2,label=lab)
ax[0].set_title('Dark-energy density, today = 1',loc='left',color='#0b0b0b'); ax[0].set_xlabel('redshift z')
ax[1].set_title('Equation of state w (−1 = constant)',loc='left',color='#0b0b0b'); ax[1].set_xlabel('redshift z'); ax[1].set_ylim(-2.4,-0.6)
ax[2].set_title('Expansion rate vs standard model [%]',loc='left',color='#0b0b0b'); ax[2].set_xlabel('redshift z')
ax[0].legend(frameon=False,loc='lower left')
fig.suptitle(f"Leftover law vs DESI-type fit, both fitted to DESI DR2 BAO + {'DES-SN5YR' if (len(sys.argv)>1 and sys.argv[1]=='des') else 'Pantheon+'} + Planck priors",x=0.01,ha='left',color='#0b0b0b')
fig.tight_layout(); fig.savefig(f"/mnt/project-files/gravity-v7/de/leftover_predict_{sys.argv[1] if len(sys.argv)>1 else 'pantheon'}.png",dpi=160,facecolor='#fcfcfb')
