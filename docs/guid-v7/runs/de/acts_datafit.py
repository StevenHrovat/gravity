# Fit Steven's acts-slowed-by-clumping law to the DATA (not to DESI's CPL summary).
# Data: DESI DR2 BAO (CobayaSampler/bao_data desi_bao_dr2 ALL_GCcomb, 13 points + cov), Pantheon+ (z_HD > 0.01, STAT+SYS cov, M marginalised),
# Planck 2018 distance priors (Chen, Huang & Wang 2018, arXiv 1808.05724 Table 1, LCDM TT,TE,EE+lowE: R, l_A, omega_b, read 2026-11-04 via ar5iv).
# r_d: Aubourg et al. 2015 fitting formula; z*: Hu & Sugiyama 1996; flat; sum m_nu 0.06 eV counted in matter; N_eff 3.046.
# Models: LCDM; CPL (w0, wa: +2 params, pipeline check against DESI's +Pantheon+ result); acts laws (0 extra params, shape fixed by tracer, grown at Om 0.31).
import sys, numpy as np
from scipy.optimize import minimize
from scipy.integrate import quad
from scipy.special import erfc
sys.path.insert(0,'/mnt/project-files/gravity-v7/de')
D='/tmp/claude-0/desi/'
c=299792.458
# --- BAO
bz,bv,bq=[],[],[]
for l in open(D+'desi_gaussian_bao_ALL_GCcomb_mean.txt'):
    if l.startswith('#'): continue
    a,b,q=l.split(); bz.append(float(a)); bv.append(float(b)); bq.append(q)
bz=np.array(bz); bv=np.array(bv); bic=np.linalg.inv(np.loadtxt(D+'desi_gaussian_bao_ALL_GCcomb_cov.txt'))
# --- SN: argv[1] = 'pantheon' (default) or 'des' (DES-SN5YR Dovekie recalibration, 1820 SNe, inverse STAT+SYS cov, des-science/DES-SN5YR main, read 2026-11-04)
SNSET=sys.argv[1] if len(sys.argv)>1 else 'pantheon'
import pandas as pd
if SNSET=='pantheon':
    pp=pd.read_csv(D+'pp.dat',sep=r'\s+')
    cov=np.loadtxt(D+'pp.cov',skiprows=1).reshape(len(pp),len(pp))
    m=(pp.zHD>0.01).values
    zs=pp.zHD.values[m]; zh=pp.zHEL.values[m]; mb=pp.m_b_corr.values[m]
    sic=np.linalg.inv(cov[np.ix_(m,m)])
else:
    rows=[l.split() for l in open(D+'dovekie.csv') if l.startswith('SN:')]
    zs=np.array([float(r[3]) for r in rows]); zh=np.array([float(r[4]) for r in rows]); mb=np.array([float(r[5]) for r in rows])
    dz=np.load(D+'des_ss.npz'); n=int(dz['nsn'][0]); sic=np.zeros((n,n)); sic[np.triu_indices(n)]=dz['cov']; il=np.tril_indices(n,-1); sic[il]=sic.T[il]
    m=np.ones(n,bool)
sone=sic.sum()
print('SN set:',SNSET,'N =',len(zs))
# --- CMB distance priors
cm=np.array([1.7502,301.471,0.02236]); cs=np.array([0.0046,0.0895,0.00015])
cr=np.array([[1,0.46,-0.66],[0.46,1,-0.33],[-0.66,-0.33,1]]); cic=np.linalg.inv(cr*np.outer(cs,cs))
# --- tracers (from acts_scan, Om fixed 0.31)
Om0,OL0,h0=0.31,0.69,0.677
Hq=lambda z: np.sqrt(Om0*(1+z)**3+OL0); dtdz=lambda z: 1/((1+z)*Hq(z))
psi=lambda z:(1+z)**2.7/(1+((1+z)/2.9)**5.6)
Gam=Om0*h0
def T(k):
    q=k/Gam; return np.log(1+2.34*q)/(2.34*q)*(1+3.89*q+(16.1*q)**2+(5.46*q)**3+(6.71*q)**4)**-0.25
def sig2(R):
    f=lambda lk: np.exp(lk)**3.965*T(np.exp(lk))**2*(3*(np.sin(np.exp(lk)*R)-np.exp(lk)*R*np.cos(np.exp(lk)*R))/(np.exp(lk)*R)**3)**2
    return quad(f,np.log(1e-4),np.log(1e4),limit=600)[0]
norm=0.81**2/sig2(8.0); rhom=2.775e11*Om0
def g(z):
    Omz=Om0*(1+z)**3/Hq(z)**2; OLz=OL0/Hq(z)**2
    return 2.5*Omz/(Omz**(4/7)-OLz+(1+Omz/2)*(1+OLz/70))
Dg=lambda z: g(z)/(1+z)/g(0)
sig=lambda M: np.sqrt(norm*sig2((3*M/(4*np.pi*rhom))**(1/3)))
fcoll=lambda z,s: erfc(1.686/(np.sqrt(2)*s*Dg(z)))
tz=np.concatenate([np.linspace(0,3,61),np.linspace(3.2,12,45)])
s8=sig(1e8)
def collrate(z,e=1e-3): return (fcoll(max(z-e,0),s8)-fcoll(z+e,s8))/((z+e)-max(z-e,0))/dtdz(z)
cumS=np.array([quad(lambda x: psi(x)*dtdz(x),z,30,limit=200)[0] for z in tz])
cumC=np.array([quad(lambda x: collrate(x)*dtdz(x),z,30,limit=200)[0] for z in tz])
tracers={}
for lM in [9,10,11,12,13]:
    s=sig(10.0**lM); un=np.array([1-fcoll(z,s) for z in tz])
    for nm,cu in [('SFR',cumS),('collapse',cumC)]:
        r=cu*un; tracers[f'acts={nm} M_esc=1e{lM}']=r/r[0]
# --- cosmology
og=2.469e-5; Neff=3.046; onu=0.06/93.14
zgrid=np.concatenate([np.linspace(0,3,601),np.geomspace(3.0001,1200,1500)])
def fDE(model,z,p):
    if model=='LCDM': return np.ones_like(z)
    if model=='CPL':
        a=1/(1+z); return a**(-3*(1+p[0]+p[1]))*np.exp(-3*p[1]*(1-a))
    return np.interp(z,tz,tracers[model],right=0.0)
def chi2(par,model):
    Om,h,ob=par[:3]; ex=par[3:]
    if not(0.1<Om<0.6 and 0.5<h<0.9 and 0.015<ob<0.03): return 1e9
    Or=og*(1+0.2271*Neff)/h**2; ODE=1-Om-Or
    E=np.sqrt(Or*(1+zgrid)**4+Om*(1+zgrid)**3+ODE*fDE(model,zgrid,ex))
    DC=np.concatenate([[0],np.cumsum(0.5*(1/E[1:]+1/E[:-1])*np.diff(zgrid))])*c/(100*h)
    om=Om*h**2; ocb=om-onu
    rd=55.154*np.exp(-72.3*(onu+0.0006)**2)/(ocb**0.25351*ob**0.12807)
    DM=np.interp(bz,zgrid,DC); DH=c/(100*h*np.interp(bz,zgrid,E)); DV=(bz*DM**2*DH)**(1/3)
    th=np.where(np.array(bq)=='DM_over_rs',DM,np.where(np.array(bq)=='DH_over_rs',DH,DV))/rd
    d=th-bv; xb=d@bic@d
    mu=5*np.log10((1+zh)*np.interp(zs,zgrid,DC))+25; dd=mb-mu; A=dd@sic@dd; Bv=(sic@dd).sum(); xs=A-Bv**2/sone
    g1=0.0783*ob**-0.238/(1+39.5*ob**0.763); g2=0.560/(1+21.1*ob**1.81)
    zst=1048*(1+0.00124*ob**-0.738)*(1+g1*om**g2)
    DMs=c/(100*h)*quad(lambda z: 1/np.sqrt(Or*(1+z)**4+Om*(1+z)**3+ODE*fDE(model,np.array([z]),ex)[0]),0,zst,limit=200)[0]
    Rb=3*ob/(4*og)
    rs=quad(lambda a: c/np.sqrt(3*(1+Rb*a))/(100*h*np.sqrt(Or+Om*a+ODE*a**4*fDE(model,np.array([1/a-1]),ex)[0])),1e-8,1/(1+zst),limit=200)[0]
    v=np.array([np.sqrt(Om)*100*h*DMs/c,np.pi*DMs/rs,ob])-cm; xc=v@cic@v
    return xb+xs+xc,(xb,xs,xc)
def fit(model,x0):
    f=lambda p: chi2(p,model)[0] if chi2(p,model)!=1e9 else 1e9
    best=None
    for dx in [0,0.01,-0.01]:
        r=minimize(lambda p: (lambda v: v if np.isscalar(v) else v[0])(chi2(p,model)),np.array(x0)+dx*np.array([1,0.5,0.01]+[1]*(len(x0)-3)),method='Nelder-Mead',options={'xatol':1e-6,'fatol':1e-4,'maxiter':6000,'maxfev':12000})
        if best is None or r.fun<best.fun: best=r
    return best
res={}
r=fit('LCDM',[0.31,0.68,0.0224]); res['LCDM']=r
x=chi2(r.x,'LCDM')[1]
print(f"LCDM: chi2 {r.fun:.2f} (BAO {x[0]:.2f}, SN {x[1]:.2f}, CMB {x[2]:.2f})  Om {r.x[0]:.4f} h {r.x[1]:.4f} ob {r.x[2]:.5f}  N_SN {m.sum()}")
r=fit('CPL',[0.31,0.68,0.0224,-0.85,-0.6]); x=chi2(r.x,'CPL')[1]
print(f"CPL : chi2 {r.fun:.2f} (BAO {x[0]:.2f}, SN {x[1]:.2f}, CMB {x[2]:.2f})  dchi2 {r.fun-res['LCDM'].fun:+.2f} (2 extra)  Om {r.x[0]:.4f} h {r.x[1]:.4f} w0 {r.x[3]:.3f} wa {r.x[4]:.3f}  [DESI DR2+CMB+Pantheon+: w0 -0.838, wa -0.62, 2.8 sigma]")
for k in tracers:
    r=fit(k,[0.31,0.68,0.0224]); x=chi2(r.x,k)[1]
    print(f"{k:24s}: chi2 {r.fun:.2f} (BAO {x[0]:.2f}, SN {x[1]:.2f}, CMB {x[2]:.2f})  dchi2 vs LCDM {r.fun-res['LCDM'].fun:+.2f} (0 extra)  Om {r.x[0]:.4f} h {r.x[1]:.4f}")
