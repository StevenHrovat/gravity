# Steven 2026-11-04 17:31Z: dark energy = pressure of acts asserting existence, slowed as existence clumps (evidence of acts stays local).
# Compare the SHAPE of DESI's dark-energy density rho_DE(z)/rho_DE(0) (CPL fits, values from memory) with activity / clumping tracers.
import numpy as np
from scipy.integrate import quad
from scipy.special import erfc
z=np.array([0,0.25,0.5,0.75,1.0,1.5,2.0,3.0])
a=1/(1+z)
desi={"DESI+CMB+Pantheon+ (w0 -0.84, wa -0.62)":(-0.838,-0.62),
      "DESI+CMB+Union3   (w0 -0.67, wa -1.09)":(-0.667,-1.09),
      "DESI+CMB+DESY5    (w0 -0.75, wa -0.86)":(-0.752,-0.86)}
def cpl(a,w0,wa): return a**(-3*(1+w0+wa))*np.exp(-3*wa*(1-a))
print("z:            "+"  ".join(f"{x:5.2f}" for x in z))
for k,(w0,wa) in desi.items():
    print(f"{k[:14]:14s}"+"  ".join(f"{v:5.2f}" for v in cpl(a,w0,wa)), " peak z =",round(1/(1-(-1-w0)/wa)-1,2))
# Tracer 1: cosmic star-formation rate density, Madau & Dickinson 2014 fit (from memory): psi ∝ (1+z)^2.7/(1+((1+z)/2.9)^5.6)
psi=lambda zz:(1+zz)**2.7/(1+((1+zz)/2.9)**5.6)
# cosmic time
Om,OL=0.31,0.69
Hz=lambda zz: np.sqrt(Om*(1+zz)**3+OL)
dtdz=lambda zz: 1/((1+zz)*Hz(zz))
cum=lambda zz: quad(lambda x: psi(x)*dtdz(x), zz, 20)[0]
# Tracer 3: fraction of matter in collapsed haloes above 1e11 Msun (Press-Schechter, BBKS, sigma8 0.81) - rough
h=0.677; Gam=Om*h
def T(k):
    q=k/Gam; return np.log(1+2.34*q)/(2.34*q)*(1+3.89*q+(16.1*q)**2+(5.46*q)**3+(6.71*q)**4)**-0.25
def sig2(R):
    f=lambda lk: (np.exp(lk))**3*np.exp(lk)**0.965*T(np.exp(lk))**2*(3*(np.sin(np.exp(lk)*R)-np.exp(lk)*R*np.cos(np.exp(lk)*R))/(np.exp(lk)*R)**3)**2
    return quad(f,np.log(1e-4),np.log(1e3),limit=400)[0]
norm=0.81**2/sig2(8.0)
rhom=2.775e11*Om  # h^2 Msun/Mpc^3 -> with M in Msun/h, R in Mpc/h
R=lambda M: (3*M/(4*np.pi*rhom))**(1/3)
def D(zz):
    g=lambda zz: 2.5*Om*(1+zz)**3/Hz(zz)**2 /((Om*(1+zz)**3/Hz(zz)**2)**(4/7)-OL/Hz(zz)**2+(1+Om*(1+zz)**3/Hz(zz)**2/2)*(1+OL/Hz(zz)**2/70))
    return g(zz)/(1+zz)/g(0)
s11=np.sqrt(norm*sig2(R(1e11*h)))
fcoll=lambda zz: erfc(1.686/(np.sqrt(2)*s11*D(zz)))
rows={"star formation rate (acts now)":np.array([psi(x) for x in z]),
      "cumulative acts (stars formed)":np.array([cum(x) for x in z]),
      "1 - f_coll (unclumped matter)":np.array([1-fcoll(x) for x in z]),
      "cumul. acts x (1-f_coll)":np.array([cum(x)*(1-fcoll(x)) for x in z])}
print(f"sigma(1e11 Msun) = {s11:.2f}; f_coll(z=0) = {fcoll(0):.2f}")
for k,v in rows.items():
    v=v/v[0]; print(f"{k[:14]:14s}"+"  ".join(f"{x:5.2f}" for x in v), "  |", k)
