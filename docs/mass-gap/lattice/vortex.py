"""Centre vortices in SU(2): do the twists of finding MG3 carry the string tension? (step 5; pre-registered in PREREG-VORTEX.md)

The MG3 twist (Gauge.lean, twisted_balanced): a network in which every local check passes and a big loop is still off by one. In SU(2)
such twists are centre vortices, sheets on which loops pick up -1. Method (Del Debbio, Faber, Greensite, Olejnik 1997; de Forcrand and
D'Elia 1999):

1. maximal centre gauge: re-key every site (a gauge transformation, which changes no physics) so that sum over links of (tr U)^2 is
   largest, i.e. every link sits as close as possible to +1 or -1;
2. centre projection: Z = sign(tr U) on every link, the vortex network alone;
3. vortex removal: U' = Z U, the field with the vortices taken out;
4. Wilson loops W(R, T) and Creutz ratios chi(R) = -ln[W(R,R) W(R-1,R-1) / (W(R,R-1) W(R-1,R))], a local estimate of the string tension
   a^2 sigma, for the full field, the projected field and the vortex-removed field.

All in unit quaternions on the GPU (cupy): U = a0 + i a.sigma, 1/2 tr U = a0. Configurations from run_su2_gpu's heat bath.

Usage: python vortex.py BETA L N_CONF SEP N_THERM SEED OUT.npz [CHAINS] [MCG_ITERS]
       python vortex.py selftest
"""

import sys
import time

import numpy as np
import cupy as cp

import run_su2_gpu as R

G = R.G


def qmul(a, b):
    a0, a1, a2, a3 = a[..., 0], a[..., 1], a[..., 2], a[..., 3]
    b0, b1, b2, b3 = b[..., 0], b[..., 1], b[..., 2], b[..., 3]
    return cp.stack([a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3,
                     a0 * b1 + b0 * a1 - (a2 * b3 - a3 * b2),
                     a0 * b2 + b0 * a2 - (a3 * b1 - a1 * b3),
                     a0 * b3 + b0 * a3 - (a1 * b2 - a2 * b1)], axis=-1)


def qconj(a):
    return a * cp.asarray([1.0, -1.0, -1.0, -1.0])


def shift(x, mu, s):
    """x has shape (B, x, y, z, t, ...); value at site + s * mu-hat."""
    return cp.roll(x, -s, axis=1 + mu)


def quaternions(g):
    """GPU gauge links (4 x (B, x, y, z, t, 2, 2)) to unit quaternions (4, B, x, y, z, t, 4)."""
    return cp.stack([cp.stack([u[..., 0, 0].real, u[..., 0, 1].imag, u[..., 0, 1].real, u[..., 0, 0].imag], axis=-1) for u in g.U])


def mcg_functional(Q):
    return float(cp.mean(Q[..., 0] ** 2))


def mcg(Q, iters, parity):
    """Maximal centre gauge by checkerboard site updates: at each site the best rotation h maximises sum_k <h, w_k>^2 over the 8 links
    touching it, i.e. h = top eigenvector of M = sum_k w_k w_k^T."""
    Q = Q.copy()
    hist = []
    for it in range(iters):
        for p in (0, 1):
            M = 0
            for mu in range(4):
                wf = qconj(Q[mu])                 # forward link U_mu(x): Re(h U) = <h, conj U>
                wb = shift(Q[mu], mu, -1)         # backward link U_mu(x - mu): Re(U h^dag) = <U, h>
                M = M + wf[..., :, None] * wf[..., None, :] + wb[..., :, None] * wb[..., None, :]
            m = parity[p]
            _, vec = cp.linalg.eigh(M[m])
            h = cp.zeros(Q.shape[1:]) + cp.asarray([1.0, 0.0, 0.0, 0.0])
            h[m] = vec[..., :, -1]
            for mu in range(4):
                Q[mu] = qmul(qmul(h, Q[mu]), qconj(shift(h, mu, 1)))
        Q /= cp.linalg.norm(Q, axis=-1, keepdims=True)
        if it % 10 == 0 or it == iters - 1:
            hist.append(mcg_functional(Q))
    return Q, hist


def wilson_loops(Q, rmax, scalar=False):
    """W(R, T) for R, T = 1..rmax averaged over sites, chains and the 6 planes. Q: quaternion links (4, B, ...) or, if scalar, real
    numbers (4, B, ...) (the centre projection)."""
    mul = (lambda a, b: a * b) if scalar else qmul
    conj = (lambda a: a) if scalar else qconj
    re = (lambda a: a) if scalar else (lambda a: a[..., 0])
    W = np.zeros((rmax + 1, rmax + 1))
    for mu in range(4):
        for nu in range(mu + 1, 4):
            lm, ln = [Q[mu]], [Q[nu]]
            for r in range(1, rmax):
                lm.append(mul(lm[-1], shift(Q[mu], mu, r)))
                ln.append(mul(ln[-1], shift(Q[nu], nu, r)))
            for Rr in range(1, rmax + 1):
                for Tt in range(1, rmax + 1):
                    a, b = lm[Rr - 1], ln[Tt - 1]
                    loop = mul(mul(a, shift(b, mu, Rr)), mul(conj(shift(a, nu, Tt)), conj(b)))
                    W[Rr, Tt] += float(cp.mean(re(loop))) / 6.0
    return W


def creutz(W):
    rmax = W.shape[0] - 1
    with np.errstate(invalid="ignore", divide="ignore"):
        return np.array([np.nan, np.nan] + [-np.log(W[r, r] * W[r - 1, r - 1] / (W[r, r - 1] * W[r - 1, r])) for r in range(2, rmax + 1)])


def make_parity(shape):
    x, y, z, t = cp.indices(shape)
    return [((x + y + z + t) % 2 == p) for p in (0, 1)]


def selftest():
    g = G.Gauge(6, 6, 2.3, nc=2, B=2, seed=3, start="hot")
    for _ in range(20):
        g.sweep(3)
    Q = quaternions(g)
    par = [cp.broadcast_to(m, Q.shape[1:-1]) for m in make_parity(g.dims)]
    W0 = wilson_loops(Q, 3)
    Qg, hist = mcg(Q, 50, par)
    W1 = wilson_loops(Qg, 3)
    inv = np.max(np.abs(W0[1:, 1:] - W1[1:, 1:]))
    mono = all(b >= a - 1e-12 for a, b in zip(hist, hist[1:]))
    print(f"gauge invariance of Wilson loops: max change {inv:.1e};  functional {hist[0]:.4f} -> {hist[-1]:.4f}, monotone: {mono}")
    print("OK" if inv < 1e-10 and mono and hist[-1] > hist[0] else "FAIL")


def main():
    if sys.argv[1] == "selftest":
        return selftest()
    beta, L, n_conf, sep, n_therm, seed, out = (float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]),
                                                 int(sys.argv[5]), int(sys.argv[6]), sys.argv[7])
    chains = int(sys.argv[8]) if len(sys.argv) > 8 else 4
    iters = int(sys.argv[9]) if len(sys.argv) > 9 else 300
    rmax = 5
    g = G.Gauge(L, L, beta, nc=2, B=chains, seed=seed, start="cold")
    t0 = time.time()
    for _ in range(n_therm):
        g.sweep(3)
    par = None
    rec = {k: [] for k in ("full", "proj", "removed", "proj_nogauge", "functional", "vortex_density")}
    for c in range(n_conf):
        for _ in range(sep):
            g.sweep(3)
        Q = quaternions(g)
        if par is None:
            par = [cp.broadcast_to(m, Q.shape[1:-1]) for m in make_parity(g.dims)]
        Qg, hist = mcg(Q, iters, par)
        Z = cp.sign(Qg[..., 0])
        rec["full"].append(wilson_loops(Qg, rmax))
        rec["proj"].append(wilson_loops(Z, rmax, scalar=True))
        rec["removed"].append(wilson_loops(Qg * Z[..., None], rmax))
        rec["proj_nogauge"].append(wilson_loops(cp.sign(Q[..., 0]), rmax, scalar=True))  # control: projection without the gauge
        rec["functional"].append(hist)
        # fraction of plaquettes pierced by a vortex: projected plaquette = -1
        pl = []
        for mu in range(4):
            for nu in range(mu + 1, 4):
                pl.append(cp.mean(Z[mu] * shift(Z[nu], mu, 1) * shift(Z[mu], nu, 1) * Z[nu] < 0))
        rec["vortex_density"].append(float(cp.mean(cp.stack(pl))))
        np.savez(out, beta=beta, L=L, chains=chains, sep=sep, iters=iters, **{k: np.array(v) for k, v in rec.items()},
                 seconds=time.time() - t0, partial=int(c < n_conf - 1))
        print(f"beta={beta} L={L} conf {c + 1}/{n_conf} functional {hist[-1]:.4f} vortex density {rec['vortex_density'][-1]:.4f} "
              f"chi(2..4) full {np.round(creutz(rec['full'][-1])[2:5], 3)} proj {np.round(creutz(rec['proj'][-1])[2:5], 3)} "
              f"removed {np.round(creutz(rec['removed'][-1])[2:5], 3)} t={time.time() - t0:.0f}s", flush=True)


if __name__ == "__main__":
    sys.exit(main())
