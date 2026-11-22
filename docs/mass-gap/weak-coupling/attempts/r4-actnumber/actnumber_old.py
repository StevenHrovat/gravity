"""The act number z(L) = E_e(L) * L of 4D SU(2) in a twisted box (round 4, attempt r4-actnumber; PREREG.md in this folder).

A lattice of L^3 x T sites (L space, T time), periodic, Wilson action S = -beta sum_p c_p (1/2) tr U_p, with 't Hooft's twist in one
spatial plane (a, b): the plaquettes P_ab at (x_a, x_b) = (L-1, L-1), for every value of the other coordinates, carry c_p = -1 (a fixed
sign sheet; 't Hooft 1979, as used on the lattice by Garcia Perez, Gonzalez-Arroyo and Martinez, hep-lat/9302007 and hep-lat/9507001,
"flipping the sign of ... plaquettes sitting at the corner"). The flux direction f is the third spatial direction. E_e is the energy of
the lowest state with one unit of electric (centre) flux along f, e_f = 1, with e parallel to the magnetic twist m_f, so e x m = 0 and
the flux state carries no fractional momentum. It is read from the Euclidean-time correlator of Polyakov loops wound along f:

  p_k(t) = (1/L^2) sum_{x_a, x_b} (1/2) tr prod_{x_f} V^(k)_f(x_a, x_b, x_f, t),

V^(k) = the f-links after k smearing steps that use only the two transverse spatial planes (fa, fb), which contain no twisted plaquette,
so the operator needs no sign and is gauge invariant (APE smearing, Albanese et al. 1987, restricted to the transverse directions as in
torelon studies; credit for the idea, our code). Under the centre transformation along f, p -> -p, so <p> = 0 exactly and the
correlator is used without vacuum subtraction. Its two-sided decay in periodic time, C(t) ~ cosh(E (T/2 - t)), gives E (analysis:
analyse_actnumber.py). z = E L is a pure number; no lattice spacing enters it.

Groups and updates
------------------
su2   heat bath (Kennedy-Pendleton) + overrelaxation, checkerboard per direction. Two code paths:
      array  numpy (CPU) or cupy (GPU) array code with the twisted staple everywhere (the reference, tested on the CPU);
      fused  the fused CUDA kernels of ../../../lattice/gpu/gauge.py (imported, unchanged; they know no twist), followed after every
             checkerboard pass of a twist-plane direction by an exact re-update of the sheet links, the only links whose staple
             contains a twisted plaquette: heat bath = a fresh draw from the correct conditional law (it does not depend on the old
             value), overrelaxation = the reflection of the value saved before the pass, with the correct staple. Exact, because a
             pass (mu, p) never reads the links it writes. The fix-up is array code (SheetFix), tested on the CPU against the array
             path with a numpy emulation of the kernel pass.
u1    exact heat bath (von Mises; boundary.vonmises) + overrelaxation, twisted complex staple (cos(theta + pi) = -cos theta).
z2    exact heat bath on angles {0, pi}, twisted staple.
2i    the binary icosahedral group (120 unit quaternions): Metropolis with proposals r U, r one of the 12 elements nearest 1 (closed under
      inverse, generating the group), several hits per link, then a snap to the nearest group element (roundoff only).

Starts ('mixed', per chain i, i mod 4): 0 twist eater with P_f = +1, 1 twist eater with P_f = -1 (SU(2), 2I; the construction of
../r3-monotone/NOTE.md section 4.1, placement in eater(), zero twisted action checked by the selftest), 2 and 3 hot (Haar; 2I: Haar
snapped to the group). U(1), Z2: cold (all 1) and hot alternating.

Usage
-----
  python actnumber.py run GROUP BETA L T SEED OUT.npz [--plane 01] [--chains 4] [--therm 500] [--meas 1000] [--every 4] [--n-or 3]
                          [--levels 0,2,6,14] [--alpha 0.5] [--path array|fused] [--cpu] [--hits 4] [--untwisted]
  python actnumber.py selftest [--gpu]
  python actnumber.py bench [--cpu]          timings of every plan entry's update, and the projected total of PLAN (GPU estimate)
GROUP su2 | u1 | z2 | 2i. --plane: the twist plane as two spatial digits (01 = xy, flux along z; 12 = yz, flux along x).
--untwisted: no sign sheet (periodic box; a reported comparison). Output OUT.npz, checkpointed every 50 measurements (partial=1).
"""

import argparse
import math
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
LATTICE = os.path.normpath(os.path.join(HERE, "..", "..", "..", "lattice"))
sys.path.insert(0, LATTICE)
import boundary as BD  # noqa: E402  (ours: imported, never edited)

qmul = BD.qmul
QSIGN = np.array([1.0, -1.0, -1.0, -1.0])


def get_xp(gpu):
    if gpu:
        import cupy as cp
        return cp
    return np


def to_host(x):
    return x.get() if hasattr(x, "get") else np.asarray(x)


def qdag(q, xp=np):
    return q * xp.asarray(QSIGN)


def sh(x, mu, s=1):
    """Field at site + s * mu-hat for arrays (B or 1, L, L, L, T, ...); numpy or cupy."""
    return BD.sh(x, mu, s)


class Rng:
    """Uniform and normal numbers for numpy or cupy."""

    def __init__(self, xp, seed):
        self.xp = xp
        self.r = np.random.default_rng(seed) if xp is np else xp.random.RandomState(seed)

    def uniform(self, shape):
        return self.r.random(shape) if self.xp is np else self.r.random_sample(shape)

    def normal(self, shape):
        return self.r.standard_normal(shape)


# ---------------------------------------------------------------------------------------------------------------------------- geometry

class Geometry:
    """L^3 x T (or an anisotropic box Ls = (Lx, Ly, Lz)), twist plane (a, b) (spatial, a < b), flux direction f; sign arrays
    c[(mu, nu)] of shape (1, Lx, Ly, Lz, T) (+-1.0). The sheet sits at (x_a, x_b) = (L_a - 1, L_b - 1)."""

    def __init__(self, L, T, plane=(0, 1), twisted=True, xp=np, Ls=None):
        Ls = tuple(Ls) if Ls is not None else (L, L, L)
        assert all(v % 2 == 0 for v in Ls) and T % 2 == 0, "checkerboard needs even sides"
        a, b = sorted(plane)
        assert 0 <= a < b <= 2
        self.Ls, self.T, self.a, self.b = Ls, T, a, b
        self.f = 3 - a - b
        self.L = Ls[self.f]  # the flux length (the extent of the act)
        self.cubic = len(set(Ls)) == 1
        self.twisted = twisted
        self.dims = Ls + (T,)
        self.xp = xp
        idx = np.indices(self.dims)
        par = idx.sum(axis=0) % 2
        self.parity_np = [par == 0, par == 1]
        self.parity = [xp.asarray(p) for p in self.parity_np]
        sheet = (idx[a] == Ls[a] - 1) & (idx[b] == Ls[b] - 1)
        self.sheet_np = sheet
        self.c = {}
        for mu in range(4):
            for nu in range(4):
                if mu == nu:
                    continue
                s = np.ones(self.dims)
                if twisted and {mu, nu} == {a, b}:
                    s[sheet] = -1.0
                self.c[(mu, nu)] = xp.asarray(s[None])

    def sites(self, mask):
        return tuple(np.asarray(v) for v in np.nonzero(mask))


# ---------------------------------------------------------------------------------------------------------------------------- staples

def staple_q(xp, U, mu, geo):
    """Twisted staple sum of link (x, mu), quaternions: local weight exp(beta (U A)_0) = exp(beta Re (1/2) tr(U A)), as
    boundary.staple_generic with each term multiplied by the sign of the plaquette it completes: c_{mu nu}(x) forward,
    c_{mu nu}(x - nu) backward."""
    A = xp.zeros_like(U[mu])
    for nu in range(4):
        if nu == mu:
            continue
        c = geo.c[(mu, nu)][..., None]
        A += c * qmul(qmul(sh(U[nu], mu), qdag(sh(U[mu], nu), xp), xp), qdag(U[nu], xp), xp)
        Unu_m = sh(U[nu], nu, -1)
        A += sh(c, nu, -1) * qmul(qmul(qdag(sh(Unu_m, mu), xp), qdag(sh(U[mu], nu, -1), xp), xp), Unu_m, xp)
    return A


def staple_c(xp, U, mu, geo):
    """Twisted complex staple for U(1) / Z2 angles: local weight exp(beta Re(e^{i theta} A)), as boundary.staple_generic times signs."""
    A = xp.zeros(U[mu].shape, dtype=complex)
    for nu in range(4):
        if nu == mu:
            continue
        c = geo.c[(mu, nu)]
        A += c * xp.exp(1j * (sh(U[nu], mu) - sh(U[mu], nu) - U[nu]))
        tn_m = sh(U[nu], nu, -1)
        A += sh(c, nu, -1) * xp.exp(1j * (-sh(tn_m, mu) - sh(U[mu], nu, -1) + tn_m))
    return A


def plaquette_field(xp, U, mu, nu, group):
    """(1/2) tr U_{mu nu}(x) (quaternion groups) or cos theta_{mu nu}(x) (u1, z2), shape (B, L, L, L, T), unsigned."""
    if group in ("su2", "2i"):
        P = qmul(qmul(U[mu], sh(U[nu], mu), xp), qmul(qdag(sh(U[mu], nu), xp), qdag(U[nu], xp), xp), xp)
        return P[..., 0]
    return xp.cos(U[mu] + sh(U[nu], mu) - sh(U[mu], nu) - U[nu])


def action(xp, U, geo, beta, group):
    """S = -beta sum_p c_p Re(1/2 tr U_p) per chain (the constant dropped)."""
    S = 0.0
    for mu in range(4):
        for nu in range(mu + 1, 4):
            S = S - beta * (geo.c[(mu, nu)] * plaquette_field(xp, U, mu, nu, group)).sum(axis=(1, 2, 3, 4))
    return S


# ---------------------------------------------------------------------------------------------------------------------------- samplers

def sample_x0(xp, alpha, rng, max_rounds=10000):
    """x0 in [-1, 1] with density sqrt(1 - x0^2) exp(alpha x0): Kennedy-Pendleton for alpha >= 0.3, direct rejection below (the GPU
    kernel's choices, su3_cuda.kp_x0), vectorised by rounds over the entries still pending; numpy or cupy."""
    a = xp.maximum(alpha.ravel(), 1e-12)
    out = xp.ones(a.shape)
    todo = xp.arange(a.size)
    for _ in range(max_rounds):
        if todo.size == 0:
            break
        aa = a[todo]
        r1, r2, r3, r4 = (rng.uniform(aa.shape) for _ in range(4))
        small = aa < 0.3
        xs = 2.0 * r1 - 1.0
        ok_s = r2 <= xp.sqrt(xp.maximum(1.0 - xs * xs, 0.0)) * xp.exp(aa * (xs - 1.0))
        x = -xp.log(1.0 - r1) / aa
        y = -xp.log(1.0 - r2) / aa
        cc = xp.cos(2 * np.pi * r3) ** 2
        delta = x + y * cc
        ok_k = r4 * r4 <= 1.0 - delta / 2.0
        val = xp.where(small, xs, 1.0 - delta)
        ok = xp.where(small, ok_s, ok_k)
        out[todo[ok]] = val[ok]
        todo = todo[~ok]
    return out.reshape(alpha.shape)


def random_unit3(xp, rng, shape):
    v = rng.normal(shape + (3,))
    return v / xp.linalg.norm(v, axis=-1, keepdims=True)


def su2_heatbath_draw(xp, A, beta, rng):
    """New links with density exp(beta (U A)_0) on SU(2), A (..., 4) a real combination of SU(2) elements."""
    k = xp.linalg.norm(A, axis=-1)
    Ahat = A / xp.maximum(k, 1e-300)[..., None]
    x0 = sample_x0(xp, beta * k, rng)
    v = random_unit3(xp, rng, k.shape)
    X = xp.concatenate([x0[..., None], v * xp.sqrt(xp.maximum(0.0, 1.0 - x0 * x0))[..., None]], axis=-1)
    return qmul(X, qdag(Ahat, xp), xp)


def su2_reflect(xp, A, Uold):
    """Overrelaxation: U -> Ahat^dag U^dag Ahat^dag (keeps (U A)_0)."""
    Ad = qdag(A / xp.maximum(xp.linalg.norm(A, axis=-1), 1e-300)[..., None], xp)
    return qmul(qmul(Ad, qdag(Uold, xp), xp), Ad, xp)


# ---------------------------------------------------------------------------------------------------------------------------- updaters

class ArraySU2:
    """SU(2) heat bath + overrelaxation in array code (numpy or cupy), twisted staple everywhere."""

    def __init__(self, geo, beta, U, seed, xp=np):
        self.geo, self.beta, self.xp = geo, beta, xp
        self.U = [xp.array(u, dtype=float) for u in U]
        self.rng = Rng(xp, seed)

    def pass_(self, mu, p, mode):
        xp = self.xp
        m = self.geo.parity[p]
        A = staple_q(xp, self.U, mu, self.geo)[:, m]
        if mode == 0:
            self.U[mu][:, m] = su2_heatbath_draw(xp, A, self.beta, self.rng)
        else:
            self.U[mu][:, m] = su2_reflect(xp, A, self.U[mu][:, m])

    def sweep(self, n_or):
        for mode in [0] + [1] * n_or:
            for mu in range(4):
                for p in (0, 1):
                    self.pass_(mu, p, mode)
        for mu in range(4):
            self.U[mu] /= self.xp.linalg.norm(self.U[mu], axis=-1, keepdims=True)

    def links(self):
        return self.U


class SheetFix:
    """Exact re-update of the sheet links after an untwisted checkerboard pass (see the module docstring). fetch(dir, sites) returns
    quaternions (B, n, 4) of the links of direction dir at the given sites (tuple of 4 index arrays); store(dir, sites, q) writes them."""

    def __init__(self, geo, beta, xp, seed, fetch, store):
        self.geo, self.beta, self.xp, self.fetch, self.store = geo, beta, xp, fetch, store
        self.rng = Rng(xp, seed)
        idx = np.indices(geo.dims)
        a, b = geo.a, geo.b
        self.sites, self.terms = {}, {}
        for mu in (a, b):
            other = b if mu == a else a
            # links of direction mu with a twisted plaquette in their staple: x_mu = L_mu-1 and x_other in {L_other-1, 0}
            on = (idx[mu] == geo.dims[mu] - 1) & ((idx[other] == geo.dims[other] - 1) | (idx[other] == 0))
            for p in (0, 1):
                m = on & geo.parity_np[p]
                s = geo.sites(m)
                self.sites[(mu, p)] = tuple(xp.asarray(v) for v in s)
                terms = []
                for nu in range(4):
                    if nu == mu:
                        continue
                    cnp = to_host(geo.c[(mu, nu)])[0]

                    def at(d):
                        return tuple(xp.asarray((s[k] + d[k]) % geo.dims[k]) for k in range(4))
                    e_mu = [0] * 4
                    e_mu[mu] = 1
                    e_nu = [0] * 4
                    e_nu[nu] = 1
                    mmn = [e_mu[k] - e_nu[k] for k in range(4)]
                    m_nu = [-e_nu[k] for k in range(4)]
                    xm = at(m_nu)
                    terms.append((nu, at(e_mu), at(e_nu), self.sites[(mu, p)], at(mmn), xm,
                                  xp.asarray(cnp[s])[None, :, None],
                                  xp.asarray(cnp[tuple(to_host(v) for v in xm)])[None, :, None]))
                self.terms[(mu, p)] = terms

    def staple(self, mu, p):
        xp, F = self.xp, self.fetch
        A = 0.0
        for (nu, x_mu, x_nu, x0, x_mmn, x_mn, c1, c2) in self.terms[(mu, p)]:
            A = A + c1 * qmul(qmul(F(nu, x_mu), qdag(F(mu, x_nu), xp), xp), qdag(F(nu, x0), xp), xp)
            A = A + c2 * qmul(qmul(qdag(F(nu, x_mmn), xp), qdag(F(mu, x_mn), xp), xp), F(nu, x_mn), xp)
        return A

    def save(self, mu):
        return {p: self.fetch(mu, self.sites[(mu, p)]) for p in (0, 1)}

    def apply(self, mu, p, mode, saved):
        A = self.staple(mu, p)
        if mode == 0:
            new = su2_heatbath_draw(self.xp, A, self.beta, self.rng)
        else:
            new = su2_reflect(self.xp, A, saved[p])
        self.store(mu, self.sites[(mu, p)], new)


class FusedSU2:
    """SU(2) on the fused kernels of gpu/gauge.py (unchanged, untwisted) + SheetFix after every pass of a twist-plane direction."""

    def __init__(self, geo, beta, U, seed):
        import cupy as cp
        sys.path.insert(0, os.path.join(LATTICE, "gpu"))
        import gauge as G
        self.cp, self.geo = cp, geo
        B = U[0].shape[0]
        self.g = G.Gauge(geo.Ls[0], geo.T, beta, nc=2, B=B, seed=seed, start="cold")
        if not geo.cubic:  # an anisotropic box: the kernels take (Nx, Ny, Nz, Nt) from g.dims; resize the arrays and RNG states
            g = self.g
            g.dims = geo.dims
            g.vol = int(np.prod(geo.dims))
            g.shape = (B,) + geo.dims + (2, 2)
            rng = np.random.default_rng(seed)
            g.state = cp.asarray(rng.integers(1, 2 ** 63, size=B * g.vol, dtype=np.uint64) | np.uint64(1))
            g.U = [cp.ascontiguousarray(cp.broadcast_to(cp.eye(2, dtype=g.cdt), g.shape)) for _ in range(4)]
        for mu in range(4):
            self.g.U[mu][...] = BD.q2m(cp.asarray(U[mu]), cp)
        gU = self.g.U

        def fetch(d, s):
            return BD.m2q(gU[d][(slice(None),) + s], cp)

        def store(d, s, q):
            gU[d][(slice(None),) + s] = BD.q2m(q, cp)
        self.fix = SheetFix(geo, beta, cp, seed + 7919, fetch, store) if geo.twisted else None

    def sweep(self, n_or):
        geo = self.geo
        for mode in [0] + [1] * n_or:
            for mu in range(4):
                fixme = self.fix is not None and mu in (geo.a, geo.b)
                saved = self.fix.save(mu) if (fixme and mode == 1) else None
                for p in (0, 1):
                    self.g.update(mu, p, mode)
                    if fixme:
                        self.fix.apply(mu, p, mode, saved)
        self.g.reunit()

    def links(self):
        return [BD.m2q(u, self.cp) for u in self.g.U]


class EmulatedFusedSU2:
    """CPU stand-in for FusedSU2 in the self-test: the 'kernel pass' is the untwisted array pass, then the same SheetFix."""

    def __init__(self, geo, beta, U, seed, xp=np):
        self.geo = geo
        self.plain = ArraySU2(Geometry(geo.L, geo.T, (geo.a, geo.b), twisted=False, xp=xp, Ls=geo.Ls), beta, U, seed, xp)
        Ul = self.plain.U

        def fetch(d, s):
            return Ul[d][(slice(None),) + s]

        def store(d, s, q):
            Ul[d][(slice(None),) + s] = q
        self.fix = SheetFix(geo, beta, xp, seed + 7919, fetch, store)

    def pass_(self, mu, p, mode, saved=None):
        self.plain.pass_(mu, p, mode)
        if mu in (self.geo.a, self.geo.b):
            self.fix.apply(mu, p, mode, saved)

    def sweep(self, n_or):
        geo = self.geo
        for mode in [0] + [1] * n_or:
            for mu in range(4):
                saved = self.fix.save(mu) if (mode == 1 and mu in (geo.a, geo.b)) else None
                for p in (0, 1):
                    self.pass_(mu, p, mode, saved)
        for mu in range(4):
            self.plain.U[mu] /= np.linalg.norm(self.plain.U[mu], axis=-1, keepdims=True)

    def links(self):
        return self.plain.U


class AbelianUpdater:
    """U(1) (heat bath + overrelaxation) or Z2 (heat bath on {0, pi}) with the twisted complex staple."""

    def __init__(self, geo, beta, U, seed, xp=np, z2=False):
        self.geo, self.beta, self.xp, self.z2 = geo, beta, xp, z2
        self.U = [xp.array(u, dtype=float) for u in U]
        self.draws = BD.Draws(xp, seed, self.U[0].shape[0])

    def pass_(self, mu, p, mode):
        xp = self.xp
        m = self.geo.parity[p]
        A = staple_c(xp, self.U, mu, self.geo)[:, m]
        if self.z2:
            p0 = 1.0 / (1.0 + xp.exp(-2.0 * self.beta * A.real))
            self.U[mu][:, m] = xp.where(self.draws.uniform(A.shape) < p0, 0.0, np.pi)
        elif mode == 0:
            kap = self.beta * xp.abs(A)
            self.U[mu][:, m] = xp.angle(xp.exp(1j * (-xp.angle(A) + BD.vonmises(xp, kap, self.draws))))
        else:
            self.U[mu][:, m] = xp.angle(xp.exp(1j * (-2 * xp.angle(A) - self.U[mu][:, m])))

    def sweep(self, n_or):
        for mode in [0] + [0 if self.z2 else 1] * n_or:
            for mu in range(4):
                for p in (0, 1):
                    self.pass_(mu, p, mode)

    def links(self):
        return self.U


def binary_icosahedral():
    """The 120 unit quaternions of 2I: 8 of (+-1, 0, 0, 0), 16 of (+-1/2)^4, 96 even permutations of (0, +-1, +-phi, +-1/phi)/2."""
    phi = (1 + 5 ** 0.5) / 2
    el = []
    for i in range(4):
        for s in (1, -1):
            v = [0.0] * 4
            v[i] = s
            el.append(v)
    for s in range(16):
        el.append([0.5 * (1 - 2 * ((s >> k) & 1)) for k in range(4)])
    even = [p for p in __import__("itertools").permutations(range(4))
            if sum(1 for i in range(4) for j in range(i + 1, 4) if p[i] > p[j]) % 2 == 0]
    base = [0.0, 0.5, phi / 2, 1 / (2 * phi)]
    for p in even:
        for s in range(8):
            v = [0.0] * 4
            signs = [1, 1 - 2 * (s & 1), 1 - 2 * ((s >> 1) & 1), 1 - 2 * ((s >> 2) & 1)]
            for k in range(4):
                v[p[k]] = base[k] * signs[k]
            el.append(v)
    E = np.unique(np.round(np.array(el), 12), axis=0)
    return E


class Metro2I:
    """2I gauge theory: Metropolis with left multiplication by one of the 12 nearest neighbours of 1, `hits` hits per link and pass."""

    def __init__(self, geo, beta, U, seed, xp=np, hits=4):
        self.geo, self.beta, self.xp, self.hits = geo, beta, xp, hits
        E = binary_icosahedral()
        self.E = xp.asarray(E)
        self.nbr = xp.asarray(E[np.isclose(E[:, 0], (1 + 5 ** 0.5) / 4)])
        self.U = [xp.array(u, dtype=float) for u in U]
        self.rng = Rng(xp, seed)
        self.acc = [0.0, 0]

    def pass_(self, mu, p, mode=0):
        xp = self.xp
        m = self.geo.parity[p]
        A = staple_q(xp, self.U, mu, self.geo)[:, m]
        u = self.U[mu][:, m]
        cur = qmul(u, A, xp)[..., 0]
        for _ in range(self.hits):
            k = xp.minimum((self.rng.uniform(cur.shape) * self.nbr.shape[0]).astype(int), self.nbr.shape[0] - 1)
            new = qmul(self.nbr[k], u, xp)
            nv = qmul(new, A, xp)[..., 0]
            ok = self.rng.uniform(cur.shape) < xp.exp(xp.minimum(self.beta * (nv - cur), 0.0))
            u = xp.where(ok[..., None], new, u)
            cur = xp.where(ok, nv, cur)
            self.acc[0] += float(ok.mean())
            self.acc[1] += 1
        self.U[mu][:, m] = u

    def snap(self):
        for mu in range(4):
            i = xp_argmax(self.xp, self.U[mu] @ self.E.T)
            self.U[mu] = self.E[i]

    def sweep(self, n_or):
        for _ in range(1 + n_or):
            for mu in range(4):
                for p in (0, 1):
                    self.pass_(mu, p)
        self.snap()

    def links(self):
        return self.U


def xp_argmax(xp, x):
    return xp.argmax(x, axis=-1)


# ---------------------------------------------------------------------------------------------------------------------------- starts

def eater(geo, B, sign=+1.0):
    """Twist eater (zero twisted action; ../r3-monotone/NOTE.md section 4.1): U_a = A = i sigma_3 on the links of direction a with
    x_a = L-1 and U_b = B = i sigma_2 on the links of direction b with x_b = L-1 (A B A^-1 B^-1 = -1), 1 elsewhere; with sign = -1 the
    f-links of the slice x_f = 0 are multiplied by -1 (Polyakov loop P_f = -1, the other classical vacuum)."""
    U = [np.zeros((B,) + geo.dims + (4,)) for _ in range(4)]
    for u in U:
        u[..., 0] = 1.0
    idx = np.indices(geo.dims)
    ma = idx[geo.a] == geo.Ls[geo.a] - 1
    mb = idx[geo.b] == geo.Ls[geo.b] - 1
    U[geo.a][:, ma] = np.array([0.0, 0.0, 0.0, 1.0])
    U[geo.b][:, mb] = np.array([0.0, 0.0, 1.0, 0.0])
    if sign < 0:
        U[geo.f][:, idx[geo.f] == 0] *= -1.0
    return U


def hot_q(geo, B, rng):
    U = []
    for _ in range(4):
        q = rng.standard_normal((B,) + geo.dims + (4,))
        U.append(q / np.linalg.norm(q, axis=-1, keepdims=True))
    return U


def initial(group, geo, B, seed, start="mixed"):
    """Starting links (numpy, host), per chain: see the module docstring."""
    rng = np.random.default_rng(seed + 101)
    if group in ("su2", "2i"):
        ep, em, hot = eater(geo, B, +1), eater(geo, B, -1), hot_q(geo, B, rng)
        if group == "2i":
            E = binary_icosahedral()
            hot = [E[np.argmax(h @ E.T, axis=-1)] for h in hot]
        U = []
        for mu in range(4):
            u = np.empty_like(ep[mu])
            for i in range(B):
                kind = i % 4 if start == "mixed" else {"eater": 0, "hot": 2}[start]
                u[i] = (ep, em, hot, hot)[kind][mu][i]
            U.append(u)
        return U
    U = []
    for _ in range(4):
        u = np.zeros((B,) + geo.dims)
        for i in range(B):
            if (start == "mixed" and i % 2 == 1) or start == "hot":
                u[i] = rng.uniform(-np.pi, np.pi, geo.dims) if group == "u1" else np.pi * rng.integers(0, 2, geo.dims)
        U.append(u)
    return U


def make_updater(group, geo, beta, U, seed, xp, path="array", hits=4):
    if group == "su2":
        if path == "fused":
            return FusedSU2(geo, beta, U, seed)
        return ArraySU2(geo, beta, U, seed, xp)
    if group == "2i":
        return Metro2I(geo, beta, U, seed, xp, hits=hits)
    return AbelianUpdater(geo, beta, U, seed, xp, z2=(group == "z2"))


# ---------------------------------------------------------------------------------------------------------------------------- measure

def flux_ops(xp, U, geo, group, levels, alpha=0.5):
    """p_k(t) for the smearing levels k in `levels` (sorted, may include 0): array (B, n_levels, T), complex for U(1).
    Smearing of the f-links with the four transverse staples in the planes (f, a) and (f, b) only, built from the unsmeared a, b links;
    SU(2)/2I: projection by normalising the quaternion; U(1): the phase of the sum; Z2: levels must be (0,)."""
    f, a, b = geo.f, geo.a, geo.b
    quat = group in ("su2", "2i")
    V = U[f]
    out = []
    nmax = max(levels)
    for k in range(nmax + 1):
        if k in levels:
            out.append(polyakov_mean(xp, V, f, quat, group))
        if k == nmax:
            break
        if group == "z2":
            raise ValueError("no smearing for Z2")
        if quat:
            S = V.copy()
            for nu in (a, b):
                S = S + alpha * qmul(qmul(U[nu], sh(V, nu), xp), qdag(sh(U[nu], f), xp), xp)
                Um = sh(U[nu], nu, -1)
                S = S + alpha * qmul(qmul(qdag(Um, xp), sh(V, nu, -1), xp), sh(Um, f), xp)
            V = S / xp.linalg.norm(S, axis=-1, keepdims=True)
        else:
            S = xp.exp(1j * V)
            for nu in (a, b):
                S = S + alpha * xp.exp(1j * (U[nu] + sh(V, nu) - sh(U[nu], f)))
                Um = sh(U[nu], nu, -1)
                S = S + alpha * xp.exp(1j * (-Um + sh(V, nu, -1) + sh(Um, f)))
            V = xp.angle(S)
    return xp.stack(out, axis=1)


def polyakov_mean(xp, V, f, quat, group):
    """(1/L^2) sum over the transverse sites of (1/2) tr prod_{x_f} V_f (U(1): exp(i sum theta)), shape (B, T)."""
    L = V.shape[1 + f]
    sl = [slice(None)] * V.ndim
    sl[1 + f] = 0
    P = V[tuple(sl)]
    for s in range(1, L):
        sl[1 + f] = s
        P = qmul(P, V[tuple(sl)], xp) if quat else P + V[tuple(sl)]
    # P has shape (B, [3 spatial minus f], T[, 4])
    if quat:
        tr = P[..., 0]
    elif group == "u1":
        tr = xp.exp(1j * P)
    else:
        tr = xp.cos(P)
    return tr.mean(axis=(1, 2))


def sheet_and_bulk(xp, U, geo, group):
    """Mean signed plaquette c_p Re(1/2 tr U_p) of the twisted ab-plane on the sheet and off it, per chain (B, 2). Translation
    invariance of the twisted theory (the sheet can be moved by a change of variables) makes the two equal in expectation."""
    P = plaquette_field(xp, U, geo.a, geo.b, group) * geo.c[(geo.a, geo.b)]
    sheet = xp.asarray(geo.sheet_np)
    return xp.stack([P[:, sheet].mean(axis=1), P[:, ~sheet].mean(axis=1)], axis=1)


def mean_plaquette(xp, U, geo, group):
    s = 0.0
    for mu in range(4):
        for nu in range(mu + 1, 4):
            s = s + (geo.c[(mu, nu)] * plaquette_field(xp, U, mu, nu, group)).mean(axis=(1, 2, 3, 4))
    return s / 6


# ---------------------------------------------------------------------------------------------------------------------------- run

def run(a):
    if a.cpu:
        os.environ["CUDA_VISIBLE_DEVICES"] = "-1"
    gpu = not a.cpu
    xp = get_xp(gpu)
    group = a.group
    plane = (int(a.plane[0]), int(a.plane[1]))
    Ls = tuple(int(v) for v in a.box.split(",")) if a.box else None
    geo = Geometry(a.L, a.T, plane, twisted=not a.untwisted, xp=xp, Ls=Ls)
    levels = [0] if group == "z2" else sorted(int(x) for x in a.levels.split(","))
    path = a.path if (group == "su2" and gpu) else "array"
    B = a.chains
    U0 = initial(group, geo, B, a.seed, a.start)
    upd = make_updater(group, geo, a.beta, U0, a.seed, xp, path=path, hits=a.hits)
    ops, plaq, sheet, times = [], [], [], []
    t0 = time.time()

    def save(partial):
        np.savez(a.out, group=group, beta=a.beta, L=geo.L, Ls=np.array(geo.Ls), T=a.T, plane=np.array(plane), f=geo.f,
                 twisted=int(geo.twisted),
                 levels=np.array(levels), chains=B, every=a.every, n_or=a.n_or, therm=a.therm, seed=a.seed, path=path,
                 start=a.start, ops=np.array(ops), plaq=np.array(plaq), sheet=np.array(sheet), partial=int(partial),
                 seconds=time.time() - t0, acc=np.array(getattr(upd, "acc", [0.0, 0])))

    for i in range(a.therm):
        upd.sweep(a.n_or)
    t_th = time.time() - t0
    print(f"{group} beta={a.beta} L={a.L} T={a.T} plane={a.plane} twisted={geo.twisted} path={path} chains={B}: "
          f"{a.therm} thermalisation sweeps in {t_th:.1f}s", flush=True)
    for m in range(a.meas):
        for _ in range(a.every):
            upd.sweep(a.n_or)
        U = upd.links()
        ops.append(to_host(flux_ops(xp, U, geo, group, levels, a.alpha)))
        plaq.append(to_host(mean_plaquette(xp, U, geo, group)))
        sheet.append(to_host(sheet_and_bulk(xp, U, geo, group)))
        if (m + 1) % 50 == 0 or m + 1 == a.meas:
            save(m + 1 < a.meas)
            o = np.array(ops)
            print(f"  meas {m + 1}/{a.meas}  plaq {np.mean(plaq):.5f}  sheet/bulk {np.mean(np.array(sheet)[..., 0]):.4f}/"
                  f"{np.mean(np.array(sheet)[..., 1]):.4f}  <|p_top|> {np.mean(np.abs(o[:, :, -1, :])):.4f}  t={time.time() - t0:.0f}s",
                  flush=True)
    save(False)
    print(f"done in {time.time() - t0:.1f}s", flush=True)
    return 0


# ---------------------------------------------------------------------------------------------------------------------------- plan

# The pre-registered production plan (PREREG.md "Runs"; queue_actnumber_gpu.ps1 runs exactly these, in this order).
# (name, group, beta, L, T, plane, twisted, chains, therm, meas_per_chain, every, levels, seed)
LV_S = "0,2,6"          # small boxes
LV_M = "0,3,8,16"       # medium
LV_L = "0,4,12,24"      # large boxes
PLAN = [
    # Amended 2026-11-22 after the round-4 review, before any data (PREREG.md "Changes before data (after the round-4 review)"):
    # every run has 8 chains (errors from the spread between chains; cold and hot starts compared), the small boxes (L sqrt(sigma)
    # <= 1.12) run 14000 sweeps per chain, the lowest points (beta 2.6 L 4, beta 2.7 L 6) and most reported extras are cut.
    # S = small box: 8 chains, 4000 thermalisation sweeps, 500 measurements every 20 sweeps; M = medium: 1500, 400 every 8;
    # B = large: 1000, 400 every 4.
    # photon gate (U(1), Coulomb phase): run first, the queue stops if it fails
    ("u1_b1.1_L4", "u1", 1.1, 4, 32, "01", True, 8, 300, 400, 4, LV_S, 4101),
    ("u1_b1.1_L6", "u1", 1.1, 6, 32, "01", True, 8, 300, 400, 4, LV_S, 4102),
    ("u1_b1.1_L8", "u1", 1.1, 8, 48, "01", True, 8, 300, 300, 4, LV_M, 4103),
    ("u1_b1.1_L10", "u1", 1.1, 10, 48, "01", True, 8, 300, 300, 4, LV_M, 4104),
    # SU(2), coarse spacing beta 2.4 (a sqrt(sigma) = 0.258)
    ("su2_b2.4_L4", "su2", 2.4, 4, 96, "01", True, 8, 4000, 500, 20, LV_S, 4201),
    ("su2_b2.4_L6", "su2", 2.4, 6, 64, "01", True, 8, 1500, 400, 8, LV_S, 4202),
    ("su2_b2.4_L8", "su2", 2.4, 8, 48, "01", True, 8, 1500, 400, 8, LV_M, 4203),
    ("su2_b2.4_L10", "su2", 2.4, 10, 32, "01", True, 8, 1000, 400, 4, LV_M, 4204),
    ("su2_b2.4_L12", "su2", 2.4, 12, 32, "01", True, 8, 1000, 400, 4, LV_L, 4205),
    ("su2_b2.4_L14", "su2", 2.4, 14, 32, "01", True, 8, 1000, 400, 4, LV_L, 4206),
    # SU(2), fine spacing beta 2.5 (a sqrt(sigma) = 0.182)
    ("su2_b2.5_L4", "su2", 2.5, 4, 128, "01", True, 8, 4000, 500, 20, LV_S, 4301),
    ("su2_b2.5_L6", "su2", 2.5, 6, 64, "01", True, 8, 4000, 500, 20, LV_S, 4302),
    ("su2_b2.5_L8", "su2", 2.5, 8, 64, "01", True, 8, 1500, 400, 8, LV_M, 4303),
    ("su2_b2.5_L10", "su2", 2.5, 10, 48, "01", True, 8, 1500, 400, 8, LV_M, 4304),
    ("su2_b2.5_L12", "su2", 2.5, 12, 32, "01", True, 8, 1000, 400, 4, LV_M, 4305),
    ("su2_b2.5_L14", "su2", 2.5, 14, 32, "01", True, 8, 1000, 400, 4, LV_L, 4306),
    ("su2_b2.5_L16", "su2", 2.5, 16, 32, "01", True, 8, 1000, 400, 4, LV_L, 4307),
    # symmetry control: twist in the yz-plane, flux along x
    ("su2_b2.4_L6_p12", "su2", 2.4, 6, 64, "12", True, 8, 1500, 400, 8, LV_S, 4309),
    # Z2: L = 2 at beta 0.5 (deconfined) and 0.42 (confined) validated against the exact transfer matrix (exact_z2.py); beta 0.5 at
    # L = 4, 6: z must fall. Frozen 2I (beta 8): z must fall
    ("z2_b0.5_L2", "z2", 0.5, 2, 32, "01", True, 8, 300, 500, 4, "0", 4401),
    ("z2_b0.42_L2", "z2", 0.42, 2, 32, "01", True, 8, 300, 500, 4, "0", 4404),
    ("z2_b0.5_L4", "z2", 0.5, 4, 32, "01", True, 8, 300, 500, 4, "0", 4402),
    ("z2_b0.5_L6", "z2", 0.5, 6, 32, "01", True, 8, 300, 500, 4, "0", 4403),
    ("2i_b8.0_L2", "2i", 8.0, 2, 32, "01", True, 8, 300, 500, 4, LV_S, 4501),
    ("2i_b8.0_L4", "2i", 8.0, 4, 32, "01", True, 8, 300, 500, 4, LV_S, 4502),
    ("2i_b8.0_L6", "2i", 8.0, 6, 32, "01", True, 8, 300, 300, 4, LV_S, 4503),
    # small-L end at a finer spacing and a third doubling curve for the (indicative) collapse test (beta 2.6: a sqrt(sigma) = 0.140)
    ("su2_b2.6_L6", "su2", 2.6, 6, 96, "01", True, 8, 4000, 500, 20, LV_S, 4602),
    ("su2_b2.6_L8", "su2", 2.6, 8, 64, "01", True, 8, 4000, 400, 16, LV_M, 4605),
    ("su2_b2.6_L12", "su2", 2.6, 12, 48, "01", True, 8, 1000, 400, 6, LV_M, 4606),
    # reported extra: the large end at a second spacing (beta 2.3: a sqrt(sigma) = 0.350)
    ("su2_b2.3_L8", "su2", 2.3, 8, 32, "01", True, 8, 1000, 400, 4, LV_M, 4703),
    ("su2_b2.3_L10", "su2", 2.3, 10, 32, "01", True, 8, 1000, 400, 4, LV_L, 4704),
]


# Optional addendum (r4-conjw's request, PREREG.md "Optional addendum W"): the four moves of one doubling at the same beta.
# Boxes (Lx, Ly, Lz) with the twist in xy and the flux along z: (L, L, 2L) lengthened, (2L, L, 2L) widened in x; the cubes L and 2L
# come from PLAN. (L, 2L, 2L) once, as the symmetry check of the widened box. Run only on the coordinator's decision
# (queue_actnumber_gpu.ps1 -AddendumW). Same fields as PLAN plus the box.
PLAN_W = [
    # amended 2026-11-22 after the round-4 review: 8 chains everywhere; the small boxes (cube L sqrt(sigma) <= 1.1) run as the plan's
    # small boxes (4000 thermalisation sweeps, 500 measurements every 20 sweeps)
    ("su2_b2.4_box4x4x8", "su2", 2.4, 8, 48, "01", True, 8, 4000, 500, 20, LV_S, 4901, "4,4,8"),
    ("su2_b2.4_box8x4x8", "su2", 2.4, 8, 48, "01", True, 8, 4000, 500, 20, LV_S, 4902, "8,4,8"),
    ("su2_b2.4_box6x6x12", "su2", 2.4, 12, 32, "01", True, 8, 1500, 400, 8, LV_M, 4903, "6,6,12"),
    ("su2_b2.4_box12x6x12", "su2", 2.4, 12, 32, "01", True, 8, 1500, 400, 8, LV_M, 4904, "12,6,12"),
    ("su2_b2.4_box6x12x12", "su2", 2.4, 12, 32, "01", True, 8, 1500, 400, 8, LV_M, 4905, "6,12,12"),
    ("su2_b2.5_box4x4x8", "su2", 2.5, 8, 64, "01", True, 8, 4000, 500, 20, LV_S, 4911, "4,4,8"),
    ("su2_b2.5_box8x4x8", "su2", 2.5, 8, 64, "01", True, 8, 4000, 500, 20, LV_S, 4912, "8,4,8"),
    ("su2_b2.5_box6x6x12", "su2", 2.5, 12, 48, "01", True, 8, 4000, 500, 20, LV_M, 4913, "6,6,12"),
    ("su2_b2.5_box12x6x12", "su2", 2.5, 12, 48, "01", True, 8, 4000, 500, 20, LV_M, 4914, "12,6,12"),
    ("u1_b1.1_box4x4x8", "u1", 1.1, 8, 32, "01", True, 8, 300, 400, 4, LV_S, 4921, "4,4,8"),
    ("u1_b1.1_box8x4x8", "u1", 1.1, 8, 32, "01", True, 8, 300, 400, 4, LV_S, 4922, "8,4,8"),
    ("2i_b8.0_box2x2x4", "2i", 8.0, 4, 32, "01", True, 8, 300, 500, 4, LV_S, 4931, "2,2,4"),
    ("2i_b8.0_box4x2x4", "2i", 8.0, 4, 32, "01", True, 8, 300, 500, 4, LV_S, 4932, "4,2,4"),
]


def plan_args(e, out_dir, path="fused"):
    name, g, beta, L, T, plane, tw, ch, th, me, ev, lv, seed = e[:13]
    args = ["run", g, str(beta), str(L), str(T), str(seed), os.path.join(out_dir, name + ".npz"), "--plane", plane,
            "--chains", str(ch), "--therm", str(th), "--meas", str(me), "--every", str(ev), "--levels", lv, "--path", path]
    if not tw:
        args.append("--untwisted")
    if len(e) > 13:
        args += ["--box", e[13]]
    return args


def entry_geometry(e, xp):
    name, g, beta, L, T, plane, tw = e[:7]
    Ls = tuple(int(v) for v in e[13].split(",")) if len(e) > 13 else None
    return Geometry(L, T, (int(plane[0]), int(plane[1])), twisted=tw, xp=xp, Ls=Ls)


# ---------------------------------------------------------------------------------------------------------------------------- tests

def selftest(a):
    gpu = a.gpu
    if not gpu:
        os.environ["CUDA_VISIBLE_DEVICES"] = "-1"
    xp = np
    ok_all = []

    def report(name, good, detail):
        ok_all.append(bool(good))
        print(f"[{'PASS' if good else 'FAIL'}] {name}: {detail}", flush=True)

    rng = np.random.default_rng(5)
    # 1. 2I: 120 distinct unit quaternions, closed under multiplication, 12 nearest neighbours of 1
    E = binary_icosahedral()
    prod = qmul(E[:, None, :], E[None, :, :]).reshape(-1, 4)
    closed = np.abs(prod @ E.T - 1).min(axis=1).max()
    nb = int(np.isclose(E[:, 0], (1 + 5 ** 0.5) / 4).sum())
    report("2I group", E.shape[0] == 120 and np.allclose(np.linalg.norm(E, axis=1), 1) and closed < 1e-9 and nb == 12,
           f"{E.shape[0]} elements, closure defect {closed:.1e}, {nb} nearest neighbours of 1")
    for plane in ((0, 1), (1, 2), (0, 2)):
        geo = Geometry(4, 6, plane)
        # 2. the twist eater has zero twisted action and Polyakov loops +-1
        for sgn in (1, -1):
            U = eater(geo, 2, sgn)
            S = action(xp, U, geo, 1.0, "su2") + 6 * np.prod(geo.dims)
            pf = flux_ops(xp, U, geo, "su2", [0, 2])
            report(f"eater plane {plane} sign {sgn}", np.abs(S).max() < 1e-10 and np.allclose(pf, sgn),
                   f"twisted action above minimum {np.abs(S).max():.1e}; p_f = {pf[0, :, 0]}")
        # 3. twisted staple = derivative of the twisted action (one-link changes), SU(2) and U(1)
        U = hot_q(geo, 2, rng)
        err = 0.0
        for mu in range(4):
            A = staple_q(xp, U, mu, geo)
            for _ in range(3):
                s = tuple(int(rng.integers(0, n)) for n in geo.dims)
                if _ == 0:  # a sheet link
                    s = list(s)
                    s[geo.a], s[geo.b] = geo.Ls[geo.a] - 1, geo.Ls[geo.b] - 1
                    s = tuple(s)
                new = hot_q(Geometry(2, 2), 1, rng)[0][0, 0, 0, 0, 0]
                U2 = [u.copy() for u in U]
                U2[mu][(slice(None),) + s] = new
                dS = action(xp, U2, geo, 1.0, "su2") - action(xp, U, geo, 1.0, "su2")
                pred = -(qmul(new[None], A[(slice(None),) + s])[..., 0] - qmul(U[mu][(slice(None),) + s], A[(slice(None),) + s])[..., 0])
                err = max(err, float(np.abs(dS - pred).max()))
        report(f"SU(2) twisted staple plane {plane}", err < 1e-10, f"max |dS - predicted| = {err:.1e}")
        th = [rng.uniform(-np.pi, np.pi, (2,) + geo.dims) for _ in range(4)]
        err = 0.0
        for mu in range(4):
            A = staple_c(xp, th, mu, geo)
            for k in range(3):
                s = tuple(int(rng.integers(0, n)) for n in geo.dims)
                if k == 0:
                    s = list(s)
                    s[geo.a], s[geo.b] = geo.Ls[geo.a] - 1, geo.Ls[geo.b] - 1
                    s = tuple(s)
                new = rng.uniform(-np.pi, np.pi)
                th2 = [t.copy() for t in th]
                th2[mu][(slice(None),) + s] = new
                dS = action(xp, th2, geo, 1.0, "u1") - action(xp, th, geo, 1.0, "u1")
                old = th[mu][(slice(None),) + s]
                Asite = A[(slice(None),) + s]
                pred = -(np.real(np.exp(1j * new) * Asite) - np.real(np.exp(1j * old) * Asite))
                err = max(err, float(np.abs(dS - pred).max()))
        report(f"U(1) twisted staple plane {plane}", err < 1e-10, f"max |dS - predicted| = {err:.1e}")
    # 4. gauge invariance of the twisted action, the flux operators and the sheet plaquettes (SU(2), U(1))
    geo = Geometry(4, 6, (0, 1))
    U = hot_q(geo, 2, rng)
    g = hot_q(geo, 2, rng)[0]
    Ug = [qmul(qmul(g, U[mu]), qdag(sh(g, mu))) for mu in range(4)]
    d1 = np.abs(action(xp, Ug, geo, 1.0, "su2") - action(xp, U, geo, 1.0, "su2")).max()
    d2 = np.abs(flux_ops(xp, Ug, geo, "su2", [0, 3, 7]) - flux_ops(xp, U, geo, "su2", [0, 3, 7])).max()
    th = [rng.uniform(-np.pi, np.pi, (2,) + geo.dims) for _ in range(4)]
    al = rng.uniform(-np.pi, np.pi, (2,) + geo.dims)
    thg = [th[mu] + al - sh(al, mu) for mu in range(4)]
    d3 = np.abs(flux_ops(xp, thg, geo, "u1", [0, 3]) - flux_ops(xp, th, geo, "u1", [0, 3])).max()
    report("gauge invariance", max(d1, d2, d3) < 1e-10, f"action {d1:.1e}, SU(2) flux ops {d2:.1e}, U(1) flux ops {d3:.1e}")
    # 5. centre transformation along f flips every flux operator (the e_f = 1 quantum number)
    Uc = [u.copy() for u in U]
    Uc[geo.f][:, np.indices(geo.dims)[geo.f] == 1] *= -1
    d4 = np.abs(flux_ops(xp, Uc, geo, "su2", [0, 3]) + flux_ops(xp, U, geo, "su2", [0, 3])).max()
    d5 = np.abs(action(xp, Uc, geo, 1.0, "su2") - action(xp, U, geo, 1.0, "su2")).max()
    report("centre symmetry", d4 < 1e-10 and d5 < 1e-10, f"p_f + p_f(centre) = {d4:.1e}, action change {d5:.1e}")
    # 6. heat-bath sampler exact: KS test of x0 against sqrt(1 - x^2) exp(alpha x)
    xs = np.linspace(-1, 1, 20001)
    for al in (0.15, 2.0, 9.0):
        x0 = sample_x0(np, np.full(40000, al), Rng(np, 11))
        D, p = BD.ks_pvalue(x0, BD.tab_cdf(xs, np.sqrt(1 - xs ** 2) * np.exp(al * (xs - 1))))
        report(f"x0 sampler alpha={al}", p > 1e-3, f"KS p = {p:.3f}")
    # 7. SheetFix: overrelaxation through the emulated fused path equals the twisted array overrelaxation exactly
    geo = Geometry(4, 4, (0, 1))
    U = hot_q(geo, 2, rng)
    arr = ArraySU2(geo, 2.4, U, 1)
    emu = EmulatedFusedSU2(geo, 2.4, U, 1)
    dmax = 0.0
    for mu in range(4):
        saved = emu.fix.save(mu) if mu in (geo.a, geo.b) else None
        for p in (0, 1):
            arr.pass_(mu, p, 1)
            emu.pass_(mu, p, 1, saved)
        dmax = max(dmax, max(np.abs(arr.U[n] - emu.plain.U[n]).max() for n in range(4)))
    report("SheetFix overrelaxation = twisted array overrelaxation", dmax < 1e-12, f"max difference {dmax:.1e}")
    # 8. signed sheet plaquette = bulk plaquette of the twisted plane (translation invariance), for every update path, and the
    #    test has power: without the fix (plain untwisted kernel on a twisted geometry) the signed sheet plaquette is far off.
    for name, mk in (("array", lambda U: ArraySU2(geo8, 2.4, U, 3)), ("emulated fused", lambda U: EmulatedFusedSU2(geo8, 2.4, U, 3)),
                     ("no fix (must fail)", lambda U: ArraySU2(Geometry(4, 8, (0, 1), twisted=False), 2.4, U, 3))):
        geo8 = Geometry(4, 8, (0, 1))
        upd = mk(eater(geo8, 4, 1))
        sb = []
        for i in range(260):
            upd.sweep(3)
            if i >= 60:
                sb.append(sheet_and_bulk(np, upd.links(), geo8, "su2"))
        sb = np.array(sb)
        d = sb[..., 0] - sb[..., 1]
        dm = d.mean()
        de = d.reshape(10, -1).mean(axis=1).std(ddof=1) / np.sqrt(10)
        good = abs(dm) < 3 * de + 0.01
        if name.startswith("no fix"):
            report(f"sheet = bulk, {name}", not good, f"sheet - bulk = {dm:.4f} +- {de:.4f} (must be far from 0)")
        else:
            report(f"sheet = bulk, {name}", good, f"sheet - bulk = {dm:.4f} +- {de:.4f}; bulk {sb[..., 1].mean():.4f}")
    # 9. U(1), Z2, 2I updates: sheet = bulk as well
    for grp, beta in (("u1", 1.1), ("z2", 0.5), ("2i", 2.4)):
        geo8 = Geometry(4, 8, (0, 1))
        upd = make_updater(grp, geo8, beta, initial(grp, geo8, 4, 9), 9, np)
        sb = []
        for i in range(160):
            upd.sweep(3 if grp == "u1" else 0)
            if i >= 40:
                sb.append(sheet_and_bulk(np, upd.links(), geo8, grp))
        sb = np.array(sb)
        d = sb[..., 0] - sb[..., 1]
        de = d.reshape(10, -1).mean(axis=1).std(ddof=1) / np.sqrt(10)
        extra = f", acceptance {upd.acc[0] / max(upd.acc[1], 1):.2f}" if grp == "2i" else ""
        report(f"sheet = bulk, {grp} beta={beta}", abs(d.mean()) < 3 * de + 0.01,
               f"sheet - bulk = {d.mean():.4f} +- {de:.4f}; bulk {sb[..., 1].mean():.4f}{extra}")
    # 10. anisotropic boxes (the four-move addendum): eater, staple, SheetFix overrelaxation, sheet = bulk on the emulated fused path
    for Ls in ((4, 2, 6), (2, 4, 4)):
        ga = Geometry(None, 4, (0, 1), Ls=Ls)
        U = eater(ga, 2, -1)
        S = action(np, U, ga, 1.0, "su2") + 6 * np.prod(ga.dims)
        pf = flux_ops(np, U, ga, "su2", [0, 2])
        U = hot_q(ga, 2, rng)
        err = 0.0
        for mu in range(4):
            A = staple_q(np, U, mu, ga)
            s = [int(rng.integers(0, n)) for n in ga.dims]
            s[ga.a], s[ga.b] = ga.Ls[ga.a] - 1, ga.Ls[ga.b] - 1
            s = tuple(s)
            new = hot_q(Geometry(2, 2), 1, rng)[0][0, 0, 0, 0, 0]
            U2 = [u.copy() for u in U]
            U2[mu][(slice(None),) + s] = new
            dS = action(np, U2, ga, 1.0, "su2") - action(np, U, ga, 1.0, "su2")
            pred = -(qmul(new[None], A[(slice(None),) + s])[..., 0] - qmul(U[mu][(slice(None),) + s], A[(slice(None),) + s])[..., 0])
            err = max(err, float(np.abs(dS - pred).max()))
        arr = ArraySU2(ga, 2.4, U, 1)
        emu = EmulatedFusedSU2(ga, 2.4, U, 1)
        dmax = 0.0
        for mu in range(4):
            saved = emu.fix.save(mu) if mu in (ga.a, ga.b) else None
            for p in (0, 1):
                arr.pass_(mu, p, 1)
                emu.pass_(mu, p, 1, saved)
            dmax = max(dmax, max(np.abs(arr.U[k] - emu.plain.U[k]).max() for k in range(4)))
        report(f"anisotropic box {Ls}", abs(S).max() < 1e-10 and np.allclose(pf, -1) and err < 1e-10 and dmax < 1e-12,
               f"eater action {np.abs(S).max():.1e}, p_f {pf[0, :, 0]}, staple {err:.1e}, SheetFix OR {dmax:.1e}")
    ga = Geometry(None, 8, (0, 1), Ls=(4, 2, 4))
    upd = EmulatedFusedSU2(ga, 2.4, eater(ga, 4, 1), 3)
    sb = []
    for i in range(260):
        upd.sweep(3)
        if i >= 60:
            sb.append(sheet_and_bulk(np, upd.links(), ga, "su2"))
    d = np.array(sb)[..., 0] - np.array(sb)[..., 1]
    de = d.reshape(10, -1).mean(axis=1).std(ddof=1) / np.sqrt(10)
    report("sheet = bulk, emulated fused, box (4, 2, 4)", abs(d.mean()) < 3 * de + 0.01, f"sheet - bulk = {d.mean():.4f} +- {de:.4f}")
    if gpu:
        gpu_tests(report, fused=not a.no_fused)
    n_ok = sum(ok_all)
    print(f"SELFTEST {'OK' if all(ok_all) else 'FAILED'} ({n_ok}/{len(ok_all)})", flush=True)
    return 0 if all(ok_all) else 1


def gpu_tests(report, fused=True):
    """GPU-only checks: the fused path's overrelaxation equals the array path's (from one configuration), and sheet = bulk on the fused
    path; the array path on cupy equals numpy for one deterministic pass. fused=False skips the fused-path checks (array fallback)."""
    import cupy as cp
    rng = np.random.default_rng(17)
    geo = Geometry(6, 8, (0, 1), xp=cp)
    U = hot_q(geo, 2, rng)
    if fused:
        arr = ArraySU2(geo, 2.4, [cp.asarray(u) for u in U], 1, cp)
        fu = FusedSU2(geo, 2.4, U, 1)
        for mu in range(4):
            saved = fu.fix.save(mu) if mu in (geo.a, geo.b) else None
            for p in (0, 1):
                arr.pass_(mu, p, 1)
                fu.g.update(mu, p, 1)
                if mu in (geo.a, geo.b):
                    fu.fix.apply(mu, p, 1, saved)
        L1 = fu.links()
        dmax = max(float(cp.abs(arr.U[n] - L1[n]).max()) for n in range(4))
        report("GPU: fused + SheetFix overrelaxation = array overrelaxation", dmax < 1e-10, f"max difference {dmax:.1e}")
        ga = Geometry(None, 8, (0, 1), xp=cp, Ls=(8, 4, 6))
        Ua = hot_q(ga, 2, rng)
        arr = ArraySU2(ga, 2.4, [cp.asarray(u) for u in Ua], 1, cp)
        fu = FusedSU2(ga, 2.4, Ua, 1)
        for mu in range(4):
            saved = fu.fix.save(mu) if mu in (ga.a, ga.b) else None
            for p in (0, 1):
                arr.pass_(mu, p, 1)
                fu.g.update(mu, p, 1)
                if mu in (ga.a, ga.b):
                    fu.fix.apply(mu, p, 1, saved)
        La = fu.links()
        da = max(float(cp.abs(arr.U[k] - La[k]).max()) for k in range(4))
        report("GPU: fused + SheetFix = array, anisotropic box (8, 4, 6)", da < 1e-10, f"max difference {da:.1e}")
    geon = Geometry(6, 8, (0, 1))
    an = ArraySU2(geon, 2.4, U, 1)
    for mu in range(4):
        for p in (0, 1):
            an.pass_(mu, p, 1)
    arr2 = ArraySU2(geo, 2.4, [cp.asarray(u) for u in U], 1, cp)
    for mu in range(4):
        for p in (0, 1):
            arr2.pass_(mu, p, 1)
    d2 = max(float(np.abs(an.U[n] - to_host(arr2.U[n])).max()) for n in range(4))
    report("GPU: cupy array overrelaxation = numpy", d2 < 1e-12, f"max difference {d2:.1e}")
    makers = [("cupy array", lambda U0: ArraySU2(geo, 2.4, [cp.asarray(u) for u in U0], 5, cp))]
    if fused:
        makers.insert(0, ("fused", lambda U0: FusedSU2(geo, 2.4, U0, 5)))
    for name, mk in makers:
        upd = mk(eater(geo, 8, 1))
        sb = []
        for i in range(400):
            upd.sweep(3)
            if i >= 100:
                sb.append(to_host(sheet_and_bulk(cp, upd.links(), geo, "su2")))
        sb = np.array(sb)
        d = sb[..., 0] - sb[..., 1]
        de = d.reshape(10, -1).mean(axis=1).std(ddof=1) / np.sqrt(10)
        report(f"GPU: sheet = bulk, {name}", abs(d.mean()) < 3 * de + 0.005, f"sheet - bulk = {d.mean():.4f} +- {de:.4f}")
    # one short run of each group on the GPU through flux_ops
    for grp in ("u1", "z2", "2i"):
        g2 = Geometry(4, 8, (0, 1), xp=cp)
        upd = make_updater(grp, g2, {"u1": 1.1, "z2": 0.5, "2i": 8.0}[grp], initial(grp, g2, 2, 3), 3, cp)
        upd.sweep(1)
        o = flux_ops(cp, upd.links(), g2, grp, [0] if grp == "z2" else [0, 2])
        report(f"GPU: {grp} update and flux ops run", bool(cp.isfinite(o).all()), f"shape {tuple(o.shape)}")


def bench(a):
    """Time one sweep of every PLAN entry's update (a few sweeps each) and project the plan's total."""
    if a.cpu:
        os.environ["CUDA_VISIBLE_DEVICES"] = "-1"
    gpu = not a.cpu
    xp = get_xp(gpu)
    total = 0.0
    seen = {}
    for e in PLAN + (PLAN_W if a.addendum else []):
        name, g, beta, L, T, plane, tw, ch, th, me, ev, lv, seed = e[:13]
        key = (g, L, T, ch, lv, tw, e[13] if len(e) > 13 else None)
        if key not in seen:
            geo = entry_geometry(e, xp)
            path = a.path if (g == "su2" and gpu) else "array"
            upd = make_updater(g, geo, beta, initial(g, geo, ch, 1), 1, xp, path=path)
            levels = [0] if g == "z2" else [int(x) for x in lv.split(",")]
            upd.sweep(3)
            sync(xp)
            n = 3 if a.cpu else 10
            t = time.time()
            for _ in range(n):
                upd.sweep(3)
            sync(xp)
            ts = (time.time() - t) / n
            t = time.time()
            for _ in range(3):
                flux_ops(xp, upd.links(), geo, g, levels)
            sync(xp)
            tm = (time.time() - t) / 3
            seen[key] = (ts, tm, int(np.prod(geo.dims)))
        ts, tm, vol = seen[key]
        sec = (th + me * ev) * ts + me * tm
        total += sec
        print(f"{name:20s} sweep {ts * 1e3:8.1f} ms ({ts / (ch * vol) * 1e9:6.0f} ns/site)  meas {tm * 1e3:7.1f} ms  "
              f"projected {sec / 60:7.1f} min", flush=True)
    print(f"PROJECTED TOTAL {total / 3600:.2f} h ({'CPU' if a.cpu else 'GPU, path ' + a.path})", flush=True)
    return 0


def sync(xp):
    if xp is not np:
        xp.cuda.Device().synchronize()


def main():
    p = argparse.ArgumentParser()
    sp = p.add_subparsers(dest="cmd", required=True)
    r = sp.add_parser("run")
    r.add_argument("group", choices=["su2", "u1", "z2", "2i"])
    r.add_argument("beta", type=float)
    r.add_argument("L", type=int)
    r.add_argument("T", type=int)
    r.add_argument("seed", type=int)
    r.add_argument("out")
    r.add_argument("--plane", default="01")
    r.add_argument("--chains", type=int, default=4)
    r.add_argument("--therm", type=int, default=500)
    r.add_argument("--meas", type=int, default=1000)
    r.add_argument("--every", type=int, default=4)
    r.add_argument("--n-or", type=int, default=3)
    r.add_argument("--levels", default="0,2,6,14")
    r.add_argument("--alpha", type=float, default=0.5)
    r.add_argument("--path", default="fused", choices=["fused", "array"])
    r.add_argument("--start", default="mixed", choices=["mixed", "eater", "hot"])
    r.add_argument("--hits", type=int, default=4)
    r.add_argument("--untwisted", action="store_true")
    r.add_argument("--box", default=None, help="anisotropic box Lx,Ly,Lz (overrides L; L is then the flux length)")
    r.add_argument("--cpu", action="store_true")
    s = sp.add_parser("selftest")
    s.add_argument("--gpu", action="store_true")
    s.add_argument("--no-fused", action="store_true")
    pn = sp.add_parser("plannames")
    pn.add_argument("--addendum", action="store_true", help="the names of PLAN_W instead")
    rp = sp.add_parser("runplan")
    rp.add_argument("name")
    rp.add_argument("outdir")
    rp.add_argument("--path", default="fused", choices=["fused", "array"])
    b = sp.add_parser("bench")
    b.add_argument("--cpu", action="store_true")
    b.add_argument("--path", default="fused", choices=["fused", "array"])
    b.add_argument("--addendum", action="store_true", help="include PLAN_W")
    a = p.parse_args()
    if a.cmd == "run":
        return run(a)
    if a.cmd == "selftest":
        return selftest(a)
    if a.cmd == "plannames":
        print(chr(10).join(e[0] for e in (PLAN_W if a.addendum else PLAN)))
        return 0
    if a.cmd == "runplan":
        e = [e for e in PLAN + PLAN_W if e[0] == a.name]
        if not e:
            print(f"no plan entry {a.name}")
            return 2
        sys.argv = [sys.argv[0]] + plan_args(e[0], a.outdir, a.path)
        return main()
    return bench(a)


if __name__ == "__main__":
    sys.exit(main())
