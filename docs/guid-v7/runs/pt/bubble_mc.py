"""Direct Monte Carlo of bubble nucleation histories for Hubble-sized patches (flat-gauge, background expansion), to check the
late-patch shortcut of late_patch.py. Exact bubble geometry: a point converts at conformal time min_i(eta_i + |x - x_i|) (phantom bubbles
never lower the minimum). Released vacuum energy redshifts as radiation from the moment of conversion."""
import sys; sys.path.insert(0, '/mnt/project-files/gravity-v7/pt')
import numpy as np, late_patch as L
FOURPI3 = 4*np.pi/3

def run(beta, npatch=20000, npts=400, seed=1, tref_off=0.18):
    rng = np.random.default_rng(seed)
    t0, t1 = -12.0/beta - 2.0, 6.0 + 60.0/beta
    ts, a, eta, rho, F, H = L.evolve(beta, t0, t1)
    tperc = ts[np.argmin(abs(F - 0.29))]
    kref = np.argmin(abs(ts - (tperc + tref_off))); R = 1/(a[kref]*H[kref])          # patch = comoving Hubble sphere at t_ref
    tend = tperc + 0.8; mask = ts <= tend; tt, aa, ee = ts[mask], a[mask], eta[mask]; eend = ee[-1]
    rate = np.exp(beta*tt)*aa**3*FOURPI3*(R + eend - ee)**3                         # expected nucleations per unit time that can reach the sphere
    cum = np.concatenate([[0], np.cumsum(0.5*(rate[1:] + rate[:-1])*np.diff(tt))]); Ntot = cum[-1]
    # evaluation grid
    kev = np.where((ts >= tperc - 0.3) & (ts <= tend))[0][::5]
    te, ae, ee_eval, rho_b = ts[kev], a[kev], eta[kev], rho[kev]
    pts = rng.normal(size=(npts, 3)); pts *= (R*rng.random(npts)**(1/3)/np.linalg.norm(pts, axis=1))[:, None]
    dmax = np.empty(npatch); dfin = np.empty(npatch)
    for p in range(npatch):
        n = rng.poisson(Ntot)
        u = np.sort(rng.random(n))*Ntot
        tb = np.interp(u, cum, tt); eb = np.interp(tb, tt, ee)
        rmax = R + eend - eb
        dirs = rng.normal(size=(n, 3)); dirs /= np.linalg.norm(dirs, axis=1)[:, None]
        xb = dirs*(rmax*rng.random(n)**(1/3))[:, None]
        econv = np.full(npts, np.inf)
        for s in range(0, n, 256):      # time-ordered chunks; stop once every point converted before the next bubble starts
            if np.all(econv < eb[s]): break
            d = np.linalg.norm(pts[:, None, :] - xb[None, s:s+256, :], axis=2) + eb[None, s:s+256]
            econv = np.minimum(econv, d.min(axis=1))
        # energy: vacuum 3 before conversion, then 3 (a_conv/a)^4
        aconv = np.interp(econv, eta, a, right=np.inf)
        conv = econv[None, :] <= ee_eval[:, None]
        rad = np.where(conv, 3.0*(aconv[None, :]/ae[:, None])**4, 3.0)
        dl = rad.mean(axis=1)/rho_b - 1
        dmax[p] = dl.max(); dfin[p] = dl[-1]
    return dict(beta=beta, R=R, tperc=tperc, Ntot=Ntot, dmax=dmax, dfin=dfin)

if __name__ == "__main__":
    beta = float(sys.argv[1]); npatch = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
    r = run(beta, npatch)
    d = r['dmax']
    print(f"beta/H {beta}: patches {npatch}, expected bubbles reaching a patch {r['Ntot']:.0f}; mean delta at end {r['dfin'].mean():+.4f} (should be ~0)")
    for thr in (0.05, 0.1, 0.2, 0.3, 0.4, 0.5, 0.67, 1.0, 2.0, 4.0, 5.0):
        k = int((d >= thr).sum()); print(f"  P(delta_max >= {thr}) = {k}/{npatch} = {k/npatch:.2e}")
    np.save(f"/mnt/project-files/gravity-v7/pt/bubble_mc_b{beta:g}.npy", d)
