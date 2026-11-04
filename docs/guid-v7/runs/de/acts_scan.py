# Sensitivity scan of Steven's 17:31Z driver: rho_DE(t) ∝ [evidence of acts accumulated up to t] x [fraction still unclumped at t, above M_esc].
# Evidence is trapped at the CURRENT time (old evidence swallowed as regions clump): the only way to get a peak.
# Acts: (A) star formation (Madau-Dickinson 2014 fit, from memory) or (B) matter collapsing into haloes > 1e8 Msun/h (Press-Schechter, no external number).
# Output: CPL fit (w0, wa) over z 0-2.5, peak z, bump size, value at z=2; compare with DESI DR2 (from memory).
import numpy as np
from scipy.integrate import quad
from scipy.special import erfc
from scipy.optimize import least_squares
Om,OL,h=0.31,0.69,0.677
Hz=lambda z: np.sqrt(Om*(1+z)**3+OL)
dtdz=lambda z: 1/((1+z)*Hz(z))
psi=lambda z:(1+z)**2.7/(1+((1+z)/2.9)**5.6)
Gam=Om*h
def T(k):
    q=k/Gam; return np.log(1+2.34*q)/(2.34*q)*(1+3.89*q+(16.1*q)**2+(5.46*q)**3+(6.71*q)**4)**-0.25
def sig2(R):
    f=lambda lk: np.exp(lk)**3.965*T(np.exp(lk))**2*(3*(np.sin(np.exp(lk)*R)-np.exp(lk)*R*np.cos(np.exp(lk)*R))/(np.exp(lk)*R)**3)**2
    return quad(f,np.log(1e-4),np.log(1e4),limit=600)[0]
norm=0.81**2/sig2(8.0)
rhom=2.775e11*Om
Rof=lambda M:(3*M/(4*np.pi*rhom))**(1/3)
def g(z):
    Omz=Om*(1+z)**3/Hz(z)**2; OLz=OL/Hz(z)**2
    return 2.5*Omz/(Omz**(4/7)-OLz+(1+Omz/2)*(1+OLz/70))
D=lambda z: g(z)/(1+z)/g(0)
sig=lambda M: np.sqrt(norm*sig2(Rof(M)))
fcoll=lambda z,s: erfc(1.686/(np.sqrt(2)*s*D(z)))
zg=np.linspace(0,2.5,51); ag=1/(1+zg)
s8=sig(1e8)
acts={"SFR":lambda z: psi(z),
      "collapse":lambda z: -(fcoll(z+1e-3,s8)-fcoll(z-1e-3 if z>1e-3 else 0,s8))/((2e-3 if z>1e-3 else 1e-3))/dtdz(z)}
cum={k:np.array([quad(lambda x: f(x)*dtdz(x), z, 30, limit=200)[0] for z in zg]) for k,f in acts.items()}
def cplfit(r):
    res=least_squares(lambda p: np.log(ag**(-3*(1+p[0]+p[1]))*np.exp(-3*p[1]*(1-ag)))-np.log(r),[-0.9,-0.3])
    return res.x
print("DESI DR2 (from memory): Pantheon+ w0 -0.84 wa -0.62 | Union3 -0.67/-1.09 | DESY5 -0.75/-0.86; peak z 0.35-0.44, bump 6-18%, rho(z=2) ~0.73-0.76")
print(f"{'acts':9s}{'M_esc':>7s}{'fcoll0':>7s}{'peak z':>7s}{'bump%':>7s}{'r(z=2)':>7s}{'w0':>7s}{'wa':>7s}")
out=[]
for k in acts:
    for lM in [9,10,11,12,13]:
        s=sig(10**lM)
        r=cum[k]*np.array([1-fcoll(z,s) for z in zg]); r=r/r[0]
        i=np.argmax(r); w0,wa=cplfit(r)
        print(f"{k:9s}{lM:7d}{fcoll(0,s):7.2f}{zg[i]:7.2f}{100*(r[i]-1):7.1f}{np.interp(2,zg,r):7.2f}{w0:7.2f}{wa:7.2f}")
        out.append((k,lM,r))
# one-parameter strengthening: rho ∝ tracer^p (p=1 is Steven's form as stated); report p that matches a 12% bump for the best shape
print("\npower p on the tracer (rho ∝ tracer^p), SFR acts:")
for lM in [10,11,12]:
    s=sig(10**lM); r=cum["SFR"]*np.array([1-fcoll(z,s) for z in zg]); r=r/r[0]
    for p in [1,2,3]:
        rp=r**p; i=np.argmax(rp); w0,wa=cplfit(rp)
        print(f"  M_esc 1e{lM} p={p}: peak z {zg[i]:.2f} bump {100*(rp[i]-1):5.1f}%  r(2) {np.interp(2,zg,rp):.2f}  w0 {w0:.2f} wa {wa:.2f}")
