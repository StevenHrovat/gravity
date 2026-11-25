"""GPU pure-gauge SU(N) lattice (Wilson action): Python layer over the fused kernels in su3_cuda.py."""
import numpy as np
import cupy as cp
import su3_cuda as K


def host(x): return x.get() if hasattr(x, "get") else np.asarray(x)


class Gauge:
    def __init__(self, ns, nt, beta, nc=3, B=1, seed=1, start="cold", single=False):
        self.dims = (ns, ns, ns, nt)
        self.nc, self.B = nc, B
        self.vol = ns ** 3 * nt
        self.beta_host = np.broadcast_to(np.asarray(beta, float).reshape(-1), (B,)).copy()
        self.beta = cp.asarray(self.beta_host)
        self.single = single
        self.cdt = cp.complex64 if single else cp.complex128
        self.mod = K.module(nc, single)
        self.shape = (B,) + self.dims + (nc, nc)
        rng = np.random.default_rng(seed)
        self.state = cp.asarray(rng.integers(1, 2 ** 63, size=B * self.vol, dtype=np.uint64) | np.uint64(1))
        if start == "cold":
            eye = cp.eye(nc, dtype=self.cdt)
            self.U = [cp.ascontiguousarray(cp.broadcast_to(eye, self.shape)) for _ in range(4)]
        else:
            cp.random.seed(seed)
            self.U = []
            for _ in range(4):
                G = (cp.random.standard_normal(self.shape) + 1j * cp.random.standard_normal(self.shape)).astype(self.cdt)
                self.U.append(G)
            self.reunit()

    def _args(self):
        return (self.B,) + self.dims

    def reunit(self):
        n = self.B * self.vol
        g, b = K._grid(n)
        for u in self.U: self.mod.get_function("reunit")(g, b, (u, np.int64(n)))

    def update(self, mu, parity, mode):
        g, b = K._grid(self.B * self.vol)
        self.mod.get_function("upd")(g, b, (self.U[0], self.U[1], self.U[2], self.U[3], self.state, self.beta,
                                            np.int32(mu), np.int32(parity), np.int32(mode)) + tuple(np.int32(a) for a in self._args()))

    def sweep(self, n_or=4):
        for mu in range(4):
            for p in (0, 1): self.update(mu, p, 0)
        for _ in range(n_or):
            for mu in range(4):
                for p in (0, 1): self.update(mu, p, 1)
        self.reunit()

    def plaquette(self, U=None, pmask=63, per_site=False):
        U = self.U if U is None else U
        out = cp.empty(self.B * self.vol, dtype=cp.float64)
        g, b = K._grid(self.B * self.vol)
        self.mod.get_function("plaq")(g, b, (U[0], U[1], U[2], U[3], out, np.int32(pmask)) + tuple(np.int32(a) for a in self._args()))
        out = out.reshape((self.B,) + self.dims)
        if per_site: return out
        npl = bin(pmask).count("1")
        return host(out.mean(axis=(1, 2, 3, 4)) / npl)

    def polyakov(self):
        vs = self.dims[0] * self.dims[1] * self.dims[2]
        out = cp.empty(self.B * vs, dtype=self.cdt)
        g, b = K._grid(self.B * vs)
        self.mod.get_function("polyakov")(g, b, (self.U[3], out) + tuple(np.int32(a) for a in self._args()))
        return host(out).reshape((self.B,) + self.dims[:3])

    def ape(self, alpha, nsteps, niter=10, U=None):
        """returns list of 3 smeared spatial link arrays after nsteps APE iterations, starting from U (default: the current spatial links)"""
        U = [self.U[0], self.U[1], self.U[2]] if U is None else U
        g, b = K._grid(self.B * self.vol)
        f = self.mod.get_function("ape")
        for _ in range(nsteps):
            O = [cp.empty_like(u) for u in U]
            f(g, b, (U[0], U[1], U[2], O[0], O[1], O[2], np.float64(alpha), np.int32(niter)) + tuple(np.int32(a) for a in self._args()))
            U = O
        return U

    def lines(self, Ul, i, rmax, shift_dir=None):
        """products of straight lines: returns list L[r-1] = prod_{s=0}^{r-1} Ul[x + s e_dir]  for r=1..rmax (dir = i)"""
        g, b = K._grid(self.B * self.vol)
        f = self.mod.get_function("mshift")
        out = [Ul]
        cur = Ul
        for r in range(1, rmax):
            nxt = cp.empty_like(Ul)
            f(g, b, (cur, Ul, nxt, np.int32(i), np.int32(r), np.int32(0)) + tuple(np.int32(a) for a in self._args()))
            out.append(nxt); cur = nxt
        return out

    def wloop(self, P, T, i, r, t):
        out = cp.empty(self.B * self.vol, dtype=cp.float64)
        g, b = K._grid(self.B * self.vol)
        self.mod.get_function("wloop")(g, b, (P, T, out, np.int32(i), np.int32(r), np.int32(t)) + tuple(np.int32(a) for a in self._args()))
        return out.reshape((self.B,) + self.dims).mean(axis=(1, 2, 3, 4))


def tau_int(x, c=6.0):
    """integrated autocorrelation time tau = 1/2 + sum rho(t) with the automatic window W >= c*tau (Madras-Sokal); in units of the sampling interval"""
    x = np.asarray(x, float) - np.mean(x)
    n = len(x)
    f = np.fft.rfft(x, 2 * n); acf = np.fft.irfft(f * np.conj(f))[:n]
    acf = acf / acf[0]
    tau = 0.5
    for Wn in range(1, n):
        tau = 0.5 + acf[1:Wn + 1].sum()
        if Wn >= c * tau: return float(tau), Wn
    return float(tau), n


def jackknife(data, func, nbins=20):
    """data (n, ...), func: mean-over-configs -> vector; binned jackknife error. returns (estimate, error)"""
    n = data.shape[0]; nb = min(nbins, n); sz = n // nb
    bm = data[:nb * sz].reshape((nb, sz) + data.shape[1:]).mean(axis=1)
    tot = bm.sum(axis=0)
    est = func(bm.mean(axis=0))
    jk = np.array([func((tot - bm[k]) / (nb - 1)) for k in range(nb)])
    err = np.sqrt((nb - 1) / nb * ((jk - jk.mean(axis=0)) ** 2).sum(axis=0))
    return est, err
