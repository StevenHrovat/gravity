"""c8a-saturation N2 (PREREG.md): 4D Z2 lattice gauge theory on 4^4, flip probability of the 't Hooft twist sheet by
thermodynamic integration.

log(Z_tw/Z) = -2 beta * sum_{p in sheet} int_0^1 <sigma_p>_tau dtau, sheet couplings beta(1 - 2 tau); heat bath, checkerboard.
Sheet = plaquettes of the plane (0, 1) based at x0 = 0, x1 = 0 (16 plaquettes), as in the Lean `IsSheet`.
Run: py z2_twist_4d.py > z2_twist_4d.log
"""
import math
import time

import numpy as np

L = 4
D = 4
NTAU = 11
NTHERM = 500
NMEAS = 2000
NBIN = 10


def sh(A, mu, k=1):
    """A(x + k e_mu)."""
    return np.roll(A, -k, axis=mu)


def plaq(U, mu, nu):
    return U[mu] * sh(U[nu], mu) * sh(U[mu], nu) * U[nu]


def couplings(beta, tau):
    c = {}
    for mu in range(D):
        for nu in range(mu + 1, D):
            b = np.full((L,) * D, beta)
            if (mu, nu) == (0, 1):
                b[0, 0, :, :] = beta * (1 - 2 * tau)
            c[(mu, nu)] = b
    return c


def field(U, mu, c):
    h = np.zeros((L,) * D)
    for nu in range(D):
        if nu == mu:
            continue
        b = c[(min(mu, nu), max(mu, nu))]
        h += b * (sh(U[nu], mu) * sh(U[mu], nu) * U[nu])
        h += sh(b, nu, -1) * (sh(U[mu], nu, -1) * sh(sh(U[nu], mu), nu, -1) * sh(U[nu], nu, -1))
    return h


def sweep(U, c, rng, parity):
    for mu in range(D):
        for par in (0, 1):
            h = field(U, mu, c)
            prob = 1.0 / (1.0 + np.exp(-2.0 * h))
            new = np.where(rng.random((L,) * D) < prob, 1, -1).astype(np.int8)
            U[mu] = np.where(parity == par, new, U[mu])


def run(beta, rng):
    idx = np.indices((L,) * D)
    parity = idx.sum(axis=0) % 2
    U = np.ones((D,) + (L,) * D, dtype=np.int8)
    taus = np.linspace(0, 1, NTAU)
    means, errs = [], []
    for tau in taus:
        c = couplings(beta, tau)
        for _ in range(NTHERM):
            sweep(U, c, rng, parity)
        meas = np.empty(NMEAS)
        for i in range(NMEAS):
            sweep(U, c, rng, parity)
            meas[i] = plaq(U, 0, 1)[0, 0, :, :].mean()
        bins = meas.reshape(NBIN, -1).mean(axis=1)
        means.append(meas.mean())
        errs.append(bins.std(ddof=1) / math.sqrt(NBIN))
    w = np.ones(NTAU)
    w[1:-1:2] = 4
    w[2:-1:2] = 2
    w *= (taus[1] - taus[0]) / 3
    integral = float(np.dot(w, means))
    ierr = float(math.sqrt(np.dot(w ** 2, np.square(errs))))
    nsheet = L * L
    logr = -2 * beta * nsheet * integral
    logr_err = 2 * beta * nsheet * ierr
    r = math.exp(logr)
    P = r / (1 + r)
    return taus, means, errs, logr, logr_err, P


def main():
    rng = np.random.default_rng(20261122)
    print(f"4D Z2, L = {L}, sheet (0,1) at x0 = x1 = 0 ({L*L} plaquettes), NTAU = {NTAU}, NTHERM = {NTHERM}, NMEAS = {NMEAS}")
    preds = {0.05: (">=", 0.49), 0.30: (">=", 0.35), 0.60: ("<=", 0.05)}
    ok = True
    for beta in (0.05, 0.30, 0.60):
        t0 = time.time()
        taus, means, errs, logr, logr_err, P = run(beta, rng)
        print(f"\nbeta = {beta:.2f}  ({time.time() - t0:.0f} s)")
        for t, m, e in zip(taus, means, errs):
            print(f"  tau = {t:.1f}  <sigma_sheet> = {m:+.4f} +- {e:.4f}")
        Plo = 1 / (1 + math.exp(-(logr - 2 * logr_err)))
        Phi = 1 / (1 + math.exp(-(logr + 2 * logr_err)))
        op, val = preds[beta]
        passed = (P >= val) if op == ">=" else (P <= val)
        ok &= passed
        print(f"  log(Z_tw/Z) = {logr:+.3f} +- {logr_err:.3f};  P = {P:.6g}  (2 sigma: [{Plo:.6g}, {Phi:.6g}]);  "
              f"F_tw = {-logr:.3f};  prediction P {op} {val}: {'pass' if passed else 'FAIL'}")
    print("\nPASS" if ok else "\nFAIL")


if __name__ == "__main__":
    main()
