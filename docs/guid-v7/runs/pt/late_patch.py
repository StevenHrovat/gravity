"""Late-patch PBH probability in a strongly supercooled first-order transition, rebuilt from first principles.
Method of Gouttenoire & Volansky 2305.04942 (separate-universe delayed patch), coded independently.
Units: M_pl = 1, vacuum energy rho_V = 3 so H = 1 in pure vacuum. Nucleation rate per volume Gamma(t) = exp(beta*t) (H^4 units).
Background: F = exp(-I), I = 4pi/3 * int Gamma a^3 (eta - eta')^3 dt'  (exact incl. phantom bubbles).
Released vacuum energy becomes radiation. Patch: same equations, nucleation switched on only at t_i (its past light cone empty before)."""
import numpy as np, sys
FOURPI3 = 4*np.pi/3

def evolve(beta, t0, t1, ti=None, dt=None, rr0=1e-12):
    """Heun steps of (a, eta, rho_r); I and dI/dt summed over the stored nucleation history (no moment cancellation).
    Returns arrays t, a, eta, rho, F, H."""
    if dt is None: dt = min(0.004, 0.025/beta)
    n = int((t1-t0)/dt)+1; ts = t0 + dt*np.arange(n)
    A = np.empty(n); E = np.empty(n); R = np.empty(n); Fs = np.empty(n); W = np.zeros(n)   # W = Gamma a^3 dt (nucleation weight)
    a, eta, rr = 1.0, 0.0, rr0
    def fields(k, a, eta, rr):
        if k > 0:
            d = eta - E[:k]; w = W[:k]
            I = FOURPI3*np.dot(w, d**3); dI = FOURPI3*3/a*np.dot(w, d**2)
        else: I, dI = 0.0, 0.0
        F = np.exp(-I); rho = 3*F + rr; H = np.sqrt(rho/3)
        return F, H, dI
    for k in range(n):
        t = ts[k]
        A[k], E[k], R[k] = a, eta, rr
        F, H, dI = fields(k, a, eta, rr); Fs[k] = F
        W[k] = 0.0 if (ti is not None and t < ti) or F < 1e-40 else np.exp(beta*t)*a**3*dt
        da, de, dr = a*H, 1/a, -4*H*rr + 3*F*dI
        a1, e1, r1 = a+dt*da, eta+dt*de, rr+dt*dr
        F1, H1, dI1 = fields(k+1, a1, e1, r1)
        a = a + dt/2*(da + a1*H1); eta = eta + dt/2*(de + 1/a1); rr = rr + dt/2*(dr + (-4*H1*r1 + 3*F1*dI1))
    rho = 3*Fs + R
    return ts, A, E, rho, Fs, np.sqrt(rho/3)

def analyse(beta, dcs=(0.4, 0.5, 2/3), verbose=False):
    # time origin: Gamma = exp(beta t) = 1 (one bubble per Hubble volume per Hubble time) at t = 0; start early enough
    t0, t1 = -12.0/beta - 2.0, 6.0 + 60.0/beta
    ts, a, eta, rho, F, H = evolve(beta, t0, t1)
    tperc = ts[np.argmin(abs(F - 0.29))]
    res = {}
    # scan delays
    tis = tperc + np.linspace(-6.0/beta, 1.5, 76)
    dmax, tmx = [], []
    for ti in tis:
        _, ap, etap, rhop, Fp, Hp = evolve(beta, t0, t1, ti=ti)
        d = rhop/rho - 1
        k = int(np.argmax(d)); dmax.append(d[k]); tmx.append(ts[k])
    dmax = np.array(dmax); tmx = np.array(tmx)
    for dc in dcs:
        if dmax.max() < dc: res[dc] = (None, None, 0.0); continue
        j = int(np.argmax(dmax >= dc))
        # linear interpolation for t_i
        if j == 0: ti_c, tm = tis[0], tmx[0]
        else:
            w = (dc - dmax[j-1])/(dmax[j]-dmax[j-1]); ti_c = tis[j-1] + w*(tis[j]-tis[j-1]); tm = tmx[j-1] + w*(tmx[j]-tmx[j-1])
        km = int(np.argmin(abs(ts - tm))); rH = 1/(a[km]*H[km])
        m = ts <= ti_c
        integrand = np.exp(beta*ts[m])*a[m]**3*FOURPI3*(rH + eta[km] - eta[m])**3
        lnP = -np.trapezoid(integrand, ts[m])
        res[dc] = (ti_c - tperc, tm - tperc, lnP)
    return tperc, dmax.max(), res

def fit(x, dc, a=1.024, b=0.6921, c=0.8831): return -a*x**b*(1+dc)**(c*x)

if __name__ == "__main__":
    betas = [float(s) for s in sys.argv[1:]] or [4, 5, 6, 7, 8]
    print("beta/H | delta_c | delay t_i-t_perc [1/H] | t_max-t_perc | ln P_coll (ours) | ln P_coll (G-V fit) | max delta reachable (delays up to 1.5/H after percolation)")
    for b in betas:
        tp, dm, res = analyse(b)
        for dc, (dti, dtm, lnP) in res.items():
            if dti is None: print(f"{b:5.2f} | {dc:.2f} | not reached | | | {fit(b,dc):8.2f} | {dm:.3f}"); continue
            print(f"{b:5.2f} | {dc:.2f} | {dti:6.3f} | {dtm:6.3f} | {lnP:8.2f} | {fit(b,dc):8.2f} | {dm:.3f}")
        sys.stdout.flush()
