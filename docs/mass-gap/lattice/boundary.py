"""Boundary-influence instrument (Leg B of the weak-coupling phase, PREREG-BOUNDARY.md): how far into a box does its boundary reach?

A box of side ell (lattice units) has frozen boundary links and a dynamical interior. It is simulated with several boundary conditions
(BCs) and gauge-invariant interior observables are compared between them as a function of the distance from the boundary. Boxes of
fixed physical size (ell * a * sqrt(sigma) fixed) at several beta give the answer in physical units. SU(2) and U(1) (the photon test).

Geometry
--------
Box sites have coordinates 0..ell in every direction. The box is embedded in a periodic lattice of N = ell + 2 (ell even) or ell + 3
(ell odd) sites per direction, so N is even and the checkerboard of the update kernels stays valid. A link (s, mu) is DYNAMIC when
s_mu is in 0..ell-1 and s_nu is in 1..ell-1 for every nu != mu (it does not lie in a face of the box). Every other link is FROZEN: the
face links carry the boundary condition, the links outside the box are never in the staple of a dynamic link (all plaquettes of a
dynamic link lie inside the box), so they are irrelevant. Gauge freedom is left only at the interior sites (all coordinates 1..ell-1);
every observable below is invariant under it (checked by the self-test). The dynamic links are exactly the links with at least one end
in the interior cube {1..ell-1}^4: the thick cube V+ of ../weak-coupling/PROOF-NOTE.md section 3.8 (side ell - 2 there), which has no
dangling shell links, so the pure-gauge surface term of its section 3.6 does not arise. Groups: SU(2), U(1), and Z2 (U(1) angles
restricted to 0, pi: the Ising-gauge control of BLUEPRINT-REDUCTION.md section 4.2).

Boundary conditions (the face links; the interior starts from the same field and is thermalised)
-----------------------------------------------------------------------------------------------
calm     all links 1.
typical  copied from an equilibrium configuration: the periodic N^4 lattice is thermalised first (every chain its own sample), then
         its face links are frozen. The periodic stage also measures the bulk plaquette and the admissibility fractions (route 6b).
hot      face links Haar random (fixed seed, one sample per chain).
flux     the face links of a uniform abelian magnetic field in the (x, y) plane (directions 0, 1) with total flux PHI through every
         (x, y) cross-section of the box (--phi, in units of pi): U(1) default PHI = 2 pi (one Dirac unit; PHI = pi/2 for the odd
         flux witness, PROOF-NOTE C9), SU(2) the field exp(i A sigma_3) with PHI = pi, whose
         holonomy around a cross-section is the centre element -1 (one centre vortex). The flux enters through the z and t faces
         (directions 2, 3), whose (x, y) plaquettes carry PHI / ell^2 each.
twist    the same flux concentrated on a k x k patch at the centre of the z and t faces: SU(2) k = 1, i.e. a calm boundary multiplied
         by -1 on a Dirac string of links, one thin centre vortex threading the box; U(1) k = 2 (a single plaquette carrying 2 pi is
         invisible in compact U(1)); Z2 k = 1 ('flux' is not available for Z2).
Gauge: A_x(x, y) = sum_{y' >= y} f(x, y'), A_y = A_z = A_t = 0, with f the flux per (x, y) plaquette; so the loop around a cross-section
picks up PHI on the face y = 0.

Observables, per configuration and chain (all gauge invariant under interior gauge transformations)
----------------------------------------------------------------------------------------------------
plaq    (6, nd)  mean (1/2) tr U_p (SU(2)) or cos theta_p (U(1)) per plane and plaquette depth d = min over the plaquette's corners of the
                 corner's distance to the nearest face; planes (01, 02, 03, 12, 13, 23); plane 01 is the flux plane. Plaquettes all of
                 whose links are frozen are left out.
adm     (3, nd)  number of plaquettes (all planes) with shortfall 1 - (1/2) tr U_p (U(1): 1 - cos theta_p) above eps = 0.5, 1, 1.5.
sinp    (nd,)    U(1) only: mean sin theta_p of the flux plane per depth (linear in the field; zero for calm by symmetry).
loops   (ell, nd2) centred R x R Wilson loops in the flux plane, R = 1..ell, for every slice (z, t) of the box, averaged over the slices
                 at the same slice depth d2 = min(z, ell - z, t, ell - t) (d2 = 0: slices in a face, frozen). The loop of size R has its
                 lower corner at ((ell - R) // 2, (ell - R) // 2), so it encircles the centre (and the thin twist).
loops_im         U(1) only: the same with sin instead of cos.
ctrl    (ell, nd2) the same centred loops in the (z, t) plane (no flux through it), binned by the (x, y) slice depth: a control.
lines   (nd3,)   (1/2) tr of the straight line of ell links across the box in direction x, from face x = 0 to face x = ell, binned by the
                 depth of its (y, z, t) position. Invariant under interior gauge transformations (its ends are boundary sites).

Usage
-----
  python boundary.py run GROUP BETA ELL BC N_THERM N_MEAS SEED OUT.npz [--chains 4] [--n-or 3] [--every 2] [--cpu]
                         [--periodic-therm 300] [--periodic-meas 50] [--phi PHI/pi] [--smear N]
  python boundary.py couple GROUP BETA ELL BC Y N_THERM N_MEAS SEED OUT.npz [--pairs 4] [--theta 0.5] [--every 2] [--cpu] ...
                         coupled-chain upper estimate of k_V(y), Y = face | edge | corner (BLUEPRINT-REDUCTION.md section 5.1; see
                         couple() for the coupling: inverse-CDF heat bath, shared random numbers, running relative Landau alignment)
  python boundary.py selftest [--gpu]      frozen links, heat-bath exactness, coupling, alignment, gauge invariance, bulk comparison
  python boundary.py bench                 tiny GPU timing (8^4), for the GPU-time estimate
GROUP su2, u1 or z2. SU(2) 'run' uses the fused CUDA kernels of gpu/gauge.py (unchanged, wrapped: frozen links are restored after every
checkerboard pass) unless --cpu; U(1) and Z2 use the same numpy code on cupy (GPU) or numpy (--cpu); 'couple' uses array code for all
groups. --smear N adds loops_s / ctrl_s: the same loops after N APE steps inside their plane (dynamic links only). Output: OUT.npz,
checkpointed every 100 (couple: 50) measurements.
"""

import argparse
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EPS = (0.5, 1.0, 1.5)
PLANES = ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))


# ---------------------------------------------------------------------------------------------------------------------------- algebra

def qmul(a, b, xp=np):
    """Quaternion product (SU(2) as a0 + i a.sigma), last axis 4; as su2.qmul, for numpy or cupy."""
    a0, a1, a2, a3 = a[..., 0], a[..., 1], a[..., 2], a[..., 3]
    b0, b1, b2, b3 = b[..., 0], b[..., 1], b[..., 2], b[..., 3]
    return xp.stack([a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3,
                     a0 * b1 + b0 * a1 - (a2 * b3 - a3 * b2),
                     a0 * b2 + b0 * a2 - (a3 * b1 - a1 * b3),
                     a0 * b3 + b0 * a3 - (a1 * b2 - a2 * b1)], axis=-1)


class SU2Ops:
    group = "su2"

    def __init__(self, xp):
        self.xp = xp
        self.sign = xp.asarray([1.0, -1.0, -1.0, -1.0])

    def mul(self, a, b):
        return qmul(a, b, self.xp)

    def dag(self, a):
        return a * self.sign

    def re(self, a):
        return a[..., 0]

    def im(self, a):
        return None


class U1Ops:
    group = "u1"

    def __init__(self, xp):
        self.xp = xp

    def mul(self, a, b):
        return a + b

    def dag(self, a):
        return -a

    def re(self, a):
        return self.xp.cos(a)

    def im(self, a):
        return self.xp.sin(a)


def sh(x, mu, s=1):
    """Field at site + s * mu-hat; arrays (B, N, N, N, N[, 4]), mu 0..3 is axis 1 + mu (numpy or cupy, roll is the same call)."""
    mod = sys.modules[type(x).__module__.split(".")[0]]
    return mod.roll(x, -s, axis=1 + mu)


def get_xp(gpu):
    if gpu:
        import cupy as cp
        return cp
    return np


def to_host(x):
    return x.get() if hasattr(x, "get") else np.asarray(x)


# ---------------------------------------------------------------------------------------------------------------------------- geometry

class Box:
    def __init__(self, ell):
        self.ell = ell
        self.N = ell + 2 if ell % 2 == 0 else ell + 3
        N = self.N
        self.dims = (N,) * 4
        idx = np.indices(self.dims)
        self.inbox = (idx <= ell).all(axis=0)
        sd = np.minimum(idx, ell - idx).min(axis=0)
        sd[~self.inbox] = -1
        self.sdepth = sd
        self.interior = self.inbox & (sd >= 1)
        self.dyn = []
        for mu in range(4):
            ok = idx[mu] <= ell - 1
            for nu in range(4):
                if nu != mu:
                    ok = ok & (idx[nu] >= 1) & (idx[nu] <= ell - 1)
            self.dyn.append(ok)
        par = idx.sum(axis=0) % 2
        self.parity = [par == 0, par == 1]  # as the GPU kernel: (x + y + z + t) & 1
        self.c = (ell - 1) // 2

    def n_dynamic(self):
        return int(sum(d.sum() for d in self.dyn))


def roll_np(x, mu, s=1):
    return np.roll(x, -s, axis=mu)


# ---------------------------------------------------------------------------------------------------------------------------- BCs

def flux_angles(box, k, phi):
    """Link angles of the abelian field with flux phi through every (x, y) cross-section, on a k x k patch at the centre (k = ell:
    uniform). Returns (4, N, N, N, N); only direction 0 is non-zero."""
    ell, N = box.ell, box.N
    f = np.zeros((ell, ell))
    p0 = (ell - k) // 2
    f[p0:p0 + k, p0:p0 + k] = phi / k ** 2
    G = np.zeros((ell, ell + 1))
    G[:, :ell] = np.cumsum(f[:, ::-1], axis=1)[:, ::-1]  # G[x, y] = sum_{y' >= y} f[x, y']
    A = np.zeros((4,) + box.dims)
    A[0, :ell, :ell + 1] = G[:, :, None, None]
    return A


DEFAULT_PHI = {"su2": 1.0, "u1": 2.0, "z2": 1.0}  # flux through a cross-section, in units of pi
TWIST_K = {"su2": 1, "u1": 2, "z2": 1}               # patch size of the 'twist' BC


def initial_links(group, box, bc, B, seed, phi=None):
    """Initial configuration (numpy), list of 4 arrays (B, N, N, N, N[, 4]); the frozen links in it are the boundary condition. For
    'typical' it is the cold start of the periodic stage. phi: flux in units of pi (default DEFAULT_PHI). Z2: angles 0 or pi only, so
    'flux' is not available and 'twist' needs phi = 1 (one thin centre vortex)."""
    rng = np.random.default_rng(10_000 + seed)
    shape = (B,) + box.dims
    phi = DEFAULT_PHI[group] if phi is None else phi
    if group == "z2" and (bc == "flux" or (bc == "twist" and phi != 1.0)):
        raise ValueError("Z2: only calm, typical, hot and twist with phi = 1")
    if bc in ("flux", "twist"):
        k = box.ell if bc == "flux" else TWIST_K[group]
        A = flux_angles(box, k, np.pi * phi)
    else:
        A = np.zeros((4,) + box.dims)
    out = []
    for mu in range(4):
        a = np.broadcast_to(A[mu], shape)
        if group == "su2":
            q = np.zeros(shape + (4,))
            q[..., 0] = np.cos(a)
            q[..., 3] = np.sin(a)
        else:
            q = np.array(a, dtype=float)
        if bc == "hot":
            fz = ~box.dyn[mu]
            n = int(fz.sum())
            if group == "su2":
                r = rng.normal(size=(B, n, 4))
                q[:, fz] = r / np.linalg.norm(r, axis=-1, keepdims=True)
            elif group == "z2":
                q[:, fz] = np.pi * rng.integers(0, 2, size=(B, n))
            else:
                q[:, fz] = rng.uniform(-np.pi, np.pi, size=(B, n))
        out.append(q)
    return out


# ---------------------------------------------------------------------------------------------------------------------------- updates

class Draws:
    """Random numbers for B chains. With pairs=True, chains 2i and 2i + 1 receive identical numbers (synchronous coupling of a pair of
    chains, for the coupled-chain estimate of k_V(y)); each chain on its own is still an exact heat bath."""

    def __init__(self, xp, seed, B, pairs=False):
        self.xp, self.B, self.pairs = xp, B, pairs
        self.rng = np.random.default_rng(seed) if xp is np else xp.random.RandomState(seed)

    def _shape(self, shape):
        return ((shape[0] // 2,) + tuple(shape[1:])) if self.pairs else tuple(shape)

    def _expand(self, x):
        return self.xp.repeat(x, 2, axis=0) if self.pairs else x

    def uniform(self, shape):
        s = self._shape(shape)
        return self._expand(self.rng.random(s) if self.xp is np else self.rng.random_sample(s))

    def normal(self, shape):
        return self._expand(self.rng.standard_normal(self._shape(shape)))


def rejection(xp, shape, draws, nu, propose):
    """Vectorised rejection sampling on (B, n) arrays: propose(cols, u) returns (value, accepted) for the columns cols given nu uniform
    arrays of shape (B, len(cols)); columns are redrawn while any chain in them is not done (so paired chains share every draw)."""
    out = xp.zeros(shape)
    done = xp.zeros(shape, dtype=bool)
    cols = xp.arange(shape[1])
    while cols.size:
        u = [draws.uniform((shape[0], int(cols.size))) for _ in range(nu)]
        val, ok = propose(cols, u)
        new = ok & ~done[:, cols]
        sub = out[:, cols]
        sub[new] = val[new]
        out[:, cols] = sub
        d = done[:, cols] | ok
        done[:, cols] = d
        cols = cols[~d.all(axis=0)]
    return out


def kp_x0(alpha, draws):
    """x0 in [-1, 1] with density sqrt(1 - x0^2) exp(alpha x0), alpha (B, n): Kennedy-Pendleton (as su2.Lattice._kp_x0) for alpha >= 0.3,
    direct rejection below (as the GPU kernel)."""
    a_all = np.maximum(alpha, 1e-12)

    def prop(cols, u):
        a = a_all[:, cols]
        r1, r2, r3, r4 = 1.0 - u[0], u[1], 1.0 - u[2], u[3]
        lam2 = -(np.log(r1) + np.cos(2 * np.pi * r2) ** 2 * np.log(r3)) / (2 * a)
        xs = 2.0 * r2 - 1.0
        small = a < 0.3
        val = np.where(small, xs, 1.0 - 2.0 * lam2)
        ok = np.where(small, r4 <= np.sqrt(np.maximum(1.0 - xs * xs, 0.0)) * np.exp(a * (xs - 1.0)), r4 * r4 <= 1.0 - lam2)
        return val, ok
    return rejection(np, alpha.shape, draws, 4, prop)


def vonmises(xp, kappa, draws):
    """Angles with density exp(kappa cos theta) on (-pi, pi], kappa (B, n): Best and Fisher (1979), vectorised; uniform for tiny kappa."""
    k_all = xp.maximum(kappa, 1e-6)
    tau = 1.0 + xp.sqrt(1.0 + 4.0 * k_all * k_all)
    rho = (tau - xp.sqrt(2.0 * tau)) / (2.0 * k_all)
    r_all = (1.0 + rho * rho) / (2.0 * rho)

    def prop(cols, u):
        k, r = k_all[:, cols], r_all[:, cols]
        z = xp.cos(np.pi * u[0])
        f = (1.0 + r * z) / (r + z)
        c = k * (r - f)
        u2 = xp.maximum(u[1], 1e-300)
        ok = (c * (2.0 - c) - u2 > 0) | (xp.log(xp.maximum(c, 1e-300) / u2) + 1.0 - c >= 0)
        val = xp.sign(u[2] - 0.5) * xp.arccos(xp.clip(f, -1.0, 1.0))
        tiny = kappa[:, cols] < 1e-6
        val = xp.where(tiny, np.pi * (2.0 * u[2] - 1.0), val)
        return val, ok | tiny
    return rejection(xp, kappa.shape, draws, 3, prop)


_GL = np.polynomial.legendre.leggauss(64)


def _icdf(xp, logdens, lo, hi, u, iters=60):
    """Inverse CDF on [lo, hi] for a smooth density exp(logdens(t)) (elementwise parameters inside logdens), by safeguarded Newton with
    64-point Gauss-Legendre quadrature for the CDF. Continuous in the parameters and in u: the coupling that keeps paired chains close."""
    if u.size == 0:
        return u
    t, w = xp.asarray(_GL[0]), xp.asarray(_GL[1])

    def cdf(x):  # integral from lo to x, x of shape S -> S
        half = (x - lo)[..., None] / 2
        nodes = lo + half * (1 + t)
        return (half[..., 0]) * (xp.exp(logdens(nodes)) * w).sum(axis=-1)

    Z = cdf(xp.full(u.shape, hi))
    target = u * Z
    a, b = xp.full(u.shape, lo), xp.full(u.shape, hi)
    x = lo + u * (hi - lo)
    for _ in range(iters):
        F = cdf(x) - target
        a = xp.where(F <= 0, x, a)
        b = xp.where(F >= 0, x, b)
        dens = xp.exp(logdens(x[..., None]))[..., 0]
        xn = x - F / xp.maximum(dens, 1e-300)
        bad = (xn < a) | (xn > b) | ~xp.isfinite(xn)
        xn = xp.where(bad, 0.5 * (a + b), xn)
        if float(xp.max(xp.abs(xn - x))) < 1e-13:
            x = xn
            break
        x = xn
    return x


def su2_x0_icdf(xp, alpha, u):
    """x0 = -cos(phi) with phi in [0, pi] of density sin^2(phi) exp(-alpha (1 + cos phi)): the SU(2) heat-bath x0, by inverse CDF."""
    a = alpha[..., None]
    phi = _icdf(xp, lambda p: 2 * xp.log(xp.maximum(xp.sin(p), 1e-300)) - a * (1 + xp.cos(p)), 0.0, np.pi, u)
    return -xp.cos(phi)


def vonmises_icdf(xp, kappa, u):
    """Angle in (-pi, pi] with density exp(kappa (cos t - 1)), by inverse CDF."""
    k = kappa[..., None]
    return _icdf(xp, lambda t: k * (xp.cos(t) - 1), -np.pi, np.pi, u)


def staple_generic(ops, U, mu):
    """Sum of the six staples of link (x, mu): local action -beta Re[(1/2) tr (U A)] (SU(2)), as su2.Lattice.staple; for U(1) the
    complex staple of u1.U1Lattice.staple."""
    xp = ops.xp
    if ops.group == "su2":
        A = xp.zeros_like(U[mu])
        for nu in range(4):
            if nu == mu:
                continue
            A += ops.mul(ops.mul(sh(U[nu], mu), ops.dag(sh(U[mu], nu))), ops.dag(U[nu]))
            Unu_m = sh(U[nu], nu, -1)
            A += ops.mul(ops.mul(ops.dag(sh(Unu_m, mu)), ops.dag(sh(U[mu], nu, -1))), Unu_m)
        return A
    A = xp.zeros(U[mu].shape, dtype=complex)
    for nu in range(4):
        if nu == mu:
            continue
        A += xp.exp(1j * (sh(U[nu], mu) - sh(U[mu], nu) - U[nu]))
        tn_m = sh(U[nu], nu, -1)
        A += xp.exp(1j * (-sh(tn_m, mu) - sh(U[mu], nu, -1) + tn_m))
    return A


class CPUSU2:
    """SU(2) heat bath + overrelaxation in numpy or cupy array code (the reference path for the self-tests, and the coupled-chain path):
    su2.Lattice's algorithm with a batch axis and per-direction masks; only dynamic links are ever written. icdf=True draws x0 by inverse
    CDF (one uniform per link) instead of Kennedy-Pendleton rejection: exact as well, and continuous in the staple, which the
    synchronous coupling of paired chains needs."""

    def __init__(self, box, beta, U, seed, pairs=False, xp=np, icdf=False):
        self.box, self.beta, self.xp, self.icdf = box, beta, xp, icdf
        self.ops = SU2Ops(xp)
        self.U = [xp.array(u, dtype=float) for u in U]
        self.draws = Draws(xp, seed, self.U[0].shape[0], pairs)
        self.set_dynamic(box.dyn)

    def set_dynamic(self, dyn):
        xp = self.xp
        self.dyn = [xp.asarray(d) for d in dyn]
        self.masks = [[xp.asarray(dyn[mu] & self.box.parity[p]) for p in (0, 1)] for mu in range(4)]

    def heatbath(self):
        xp = self.xp
        for mu in range(4):
            for p in (0, 1):
                m = self.masks[mu][p]
                if not bool(m.any()):
                    continue
                A = staple_generic(self.ops, self.U, mu)[:, m]  # (B, n, 4)
                k = xp.linalg.norm(A, axis=-1)
                Ahat = A / xp.maximum(k, 1e-300)[..., None]
                if self.icdf:
                    x0 = su2_x0_icdf(xp, self.beta * k, self.draws.uniform(k.shape))
                else:
                    x0 = kp_x0(self.beta * k, self.draws) if xp is np else xp.asarray(kp_x0(to_host(self.beta * k), self.draws))
                v = self.draws.normal(k.shape + (3,))
                v = v / xp.linalg.norm(v, axis=-1, keepdims=True)
                X = xp.concatenate([x0[..., None], v * xp.sqrt(xp.maximum(0.0, 1.0 - x0 * x0))[..., None]], axis=-1)
                self.U[mu][:, m] = qmul(X, self.ops.dag(Ahat), xp)

    def overrelax(self):
        xp = self.xp
        for mu in range(4):
            for p in (0, 1):
                m = self.masks[mu][p]
                if not bool(m.any()):
                    continue
                A = staple_generic(self.ops, self.U, mu)[:, m]
                Ad = self.ops.dag(A / xp.maximum(xp.linalg.norm(A, axis=-1), 1e-300)[..., None])
                self.U[mu][:, m] = qmul(qmul(Ad, self.ops.dag(self.U[mu][:, m]), xp), Ad, xp)

    def sweep(self, n_or):
        xp = self.xp
        self.heatbath()
        for _ in range(n_or):
            self.overrelax()
        for mu in range(4):
            d = self.dyn[mu]
            self.U[mu][:, d] /= xp.linalg.norm(self.U[mu][:, d], axis=-1, keepdims=True)

    def links(self):
        return self.U


class U1Updater:
    """U(1) exact heat bath (von Mises, Best-Fisher) + overrelaxation, u1.U1Lattice's algorithm with a batch axis and per-direction masks;
    with z2=True the links are restricted to angles 0, pi (4D Z2 gauge theory, exact heat bath, no overrelaxation). numpy or cupy; only
    dynamic links are ever written."""

    def __init__(self, xp, box, beta, U, seed, z2=False, pairs=False, icdf=False):
        self.xp, self.box, self.beta, self.z2, self.icdf = xp, box, beta, z2, icdf
        self.ops = U1Ops(xp)
        self.U = [xp.array(u, dtype=float) for u in U]  # a copy: never write into the caller's arrays
        self.draws = Draws(xp, seed, self.U[0].shape[0], pairs)
        self.set_dynamic(box.dyn)

    def set_dynamic(self, dyn):
        xp = self.xp
        self.dyn = dyn
        self.masks = [[xp.asarray(dyn[mu] & self.box.parity[p]) for p in (0, 1)] for mu in range(4)]

    def heatbath(self):
        xp = self.xp
        for mu in range(4):
            for p in (0, 1):
                m = self.masks[mu][p]
                A = staple_generic(self.ops, self.U, mu)[:, m]
                if self.z2:
                    p0 = 1.0 / (1.0 + xp.exp(-2.0 * self.beta * A.real))  # weight exp(beta cos(theta) Re A), theta in {0, pi}
                    self.U[mu][:, m] = xp.where(self.draws.uniform(A.shape) < p0, 0.0, np.pi)
                else:
                    kap = self.beta * xp.abs(A)
                    vm = vonmises_icdf(xp, kap, self.draws.uniform(kap.shape)) if self.icdf else vonmises(xp, kap, self.draws)
                    new = -xp.angle(A) + vm
                    self.U[mu][:, m] = xp.angle(xp.exp(1j * new))

    def overrelax(self):
        if self.z2:
            return
        xp = self.xp
        for mu in range(4):
            for p in (0, 1):
                m = self.masks[mu][p]
                phi = xp.angle(staple_generic(self.ops, self.U, mu)[:, m])
                self.U[mu][:, m] = xp.angle(xp.exp(1j * (-2 * phi - self.U[mu][:, m])))

    def sweep(self, n_or):
        if self.z2:
            for _ in range(1 + n_or):  # heat bath only; a sweep = 1 + n_or heat-bath passes
                self.heatbath()
            return
        self.heatbath()
        for _ in range(n_or):
            self.overrelax()

    def links(self):
        return self.U


def q2m(q, cp):
    """Quaternion (B, ..., 4) to the 2x2 complex matrix layout of gpu/gauge.py (run_su2_gpu.to_quaternions inverted)."""
    a0, a1, a2, a3 = q[..., 0], q[..., 1], q[..., 2], q[..., 3]
    m = cp.empty(q.shape[:-1] + (2, 2), dtype=cp.complex128)
    m[..., 0, 0] = a0 + 1j * a3
    m[..., 0, 1] = a2 + 1j * a1
    m[..., 1, 0] = -a2 + 1j * a1
    m[..., 1, 1] = a0 - 1j * a3
    return m


def m2q(m, cp):
    return cp.stack([m[..., 0, 0].real, m[..., 0, 1].imag, m[..., 0, 1].real, m[..., 0, 0].imag], axis=-1)


class GPUSU2:
    """SU(2) on the fused CUDA kernels of gpu/gauge.py (unchanged). The kernels update every link of one direction and parity; the frozen
    links are restored from a copy right after every checkerboard pass. This is exact: a pass (mu, p) reads only links of other
    directions and links of direction mu at the other parity, none of which it writes, so a frozen link overwritten in the pass is
    never read before it is restored."""

    def __init__(self, box, beta, U, seed, pairs=False):
        import cupy as cp
        sys.path.insert(0, os.path.join(HERE, "gpu"))
        import gauge as G
        self.cp, self.box, self.beta = cp, box, beta
        B = U[0].shape[0]
        N = box.N
        self.g = G.Gauge(N, N, beta, nc=2, B=B, seed=seed, start="cold")
        for mu in range(4):
            self.g.U[mu][...] = q2m(cp.asarray(U[mu]), cp)
        if pairs:  # synchronous coupling: chain 2i + 1 starts with the per-site random-number states of chain 2i
            st = self.g.state.reshape(B, -1)
            st[1::2] = st[0::2]
        self.set_dynamic(box.dyn)

    def set_dynamic(self, dyn):
        """Freeze every non-dynamic link at its current value."""
        cp = self.cp
        self.dyn = dyn
        self.fmask = [cp.asarray(~d).reshape((1,) + d.shape + (1, 1)) for d in dyn]
        self.F = [u.copy() for u in self.g.U]

    def restore(self, mu):
        self.cp.copyto(self.g.U[mu], self.F[mu], where=self.fmask[mu])

    def _pass(self, mode):
        for mu in range(4):
            for p in (0, 1):
                self.g.update(mu, p, mode)
                self.restore(mu)

    def overrelax(self):
        self._pass(1)

    def sweep(self, n_or):
        g = self.g
        self._pass(0)
        for _ in range(n_or):
            self._pass(1)
        g.reunit()
        for mu in range(4):
            self.restore(mu)

    def links(self):
        return [m2q(u, self.cp) for u in self.g.U]


# ---------------------------------------------------------------------------------------------------------------------------- measure

class Measure:
    def __init__(self, ops, box, B, smear=0, alpha=0.5):
        self.ops, self.box, self.B = ops, box, B
        self.smear, self.alpha = smear, alpha
        xp = ops.xp
        extra = (1,) if ops.group == "su2" else ()
        self.smask = [xp.asarray(box.dyn[mu].reshape((1,) + box.dims + extra)) for mu in range(4)]
        ell = box.ell
        sd = box.sdepth
        # plaquette bins
        self.pidx, pc = [], []
        depths = []
        for mu, nu in PLANES:
            corners = [sd, roll_np(sd, mu), roll_np(sd, nu), roll_np(roll_np(sd, mu), nu)]
            d = np.minimum.reduce(corners)
            anyd = box.dyn[mu] | roll_np(box.dyn[nu], mu) | roll_np(box.dyn[mu], nu) | box.dyn[nu]
            valid = (np.minimum.reduce([c >= 0 for c in corners])) & (d >= 0) & anyd
            d = np.where(valid, d, -1)
            depths.append(d)
        self.nd = int(max(d.max() for d in depths)) + 1
        nb = self.nd + 1
        for d in depths:
            b = np.where(d >= 0, d, self.nd).reshape(-1)
            comb = (np.arange(B)[:, None] * nb + b[None, :]).reshape(-1)
            self.pidx.append(xp.asarray(comb))
            pc.append(np.bincount(b, minlength=nb)[:self.nd])
        self.pcount = np.array(pc)  # (6, nd)
        # slice bins for the centred loops: (z, t) in 0..ell
        r = np.arange(ell + 1)
        d2 = np.minimum.reduce(np.meshgrid(np.minimum(r, ell - r), np.minimum(r, ell - r), indexing="ij")).reshape(-1)
        self.nd2 = int(d2.max()) + 1
        oh = np.zeros((d2.size, self.nd2))
        oh[np.arange(d2.size), d2] = 1.0
        self.count2 = oh.sum(axis=0)
        self.oh2 = xp.asarray(oh / self.count2)
        # line bins: (y, z, t) in 0..ell
        g3 = np.meshgrid(*(np.minimum(r, ell - r),) * 3, indexing="ij")
        d3 = np.minimum.reduce(g3).reshape(-1)
        self.nd3 = int(d3.max()) + 1
        oh = np.zeros((d3.size, self.nd3))
        oh[np.arange(d3.size), d3] = 1.0
        self.count3 = oh.sum(axis=0)
        self.oh3 = xp.asarray(oh / self.count3)

    def _binned(self, k, vals):
        xp = self.ops.xp
        nb = self.nd + 1
        s = xp.bincount(self.pidx[k], weights=vals.reshape(-1), minlength=self.B * nb)
        return s.reshape(self.B, nb)[:, :self.nd]

    def plaquettes(self, U):
        """Per plane: the plaquette field (B, N, N, N, N[, 4])."""
        o = self.ops
        out = []
        for mu, nu in PLANES:
            out.append(o.mul(o.mul(U[mu], sh(U[nu], mu)), o.mul(o.dag(sh(U[mu], nu)), o.dag(U[nu]))))
        return out

    def smear_plane(self, U, i, j):
        """APE smearing inside the (i, j) plane only, of the dynamic links of directions i and j (frozen links stay): V -> projection
        of (1 - alpha) V + (alpha / 2) (two in-plane staples). Covariant under interior gauge transformations, so loops of smeared links
        stay gauge invariant; the loop around a whole cross-section is unchanged (its links are frozen)."""
        o, xp, al = self.ops, self.ops.xp, self.alpha
        V = list(U)

        def staples(a, b):
            up = o.mul(o.mul(V[b], sh(V[a], b)), o.dag(sh(V[b], a)))
            Vb_m = sh(V[b], b, -1)
            down = o.mul(o.mul(o.dag(Vb_m), sh(V[a], b, -1)), sh(Vb_m, a))
            return up, down

        for _ in range(self.smear):
            new = {}
            for a, b in ((i, j), (j, i)):
                up, down = staples(a, b)
                # where the sum vanishes (common in Z2) the projection is undefined: keep the link there (|sum| is gauge
                # invariant, so this stays covariant)
                if o.group == "su2":
                    M = (1 - al) * V[a] + 0.5 * al * (up + down)
                    nm = xp.linalg.norm(M, axis=-1, keepdims=True)
                    M = xp.where(nm > 1e-9, M / xp.maximum(nm, 1e-300), V[a])
                else:
                    Z = (1 - al) * xp.exp(1j * V[a]) + 0.5 * al * (xp.exp(1j * up) + xp.exp(1j * down))
                    M = xp.where(xp.abs(Z) > 1e-9, xp.angle(Z), V[a])
                new[a] = xp.where(self.smask[a], M, V[a])
            V[i], V[j] = new[i], new[j]
        return V

    def centred_loops(self, U, i, j, k, l):
        """Centred R x R loops in plane (i, j) for every slice (k, l) of the box: returns re (B, ell, nd2) and im (or None).
        Prefix products along each line, P(x) = V(0) ... V(x - 1), so a segment [a, b) is P(a)^dagger P(b) (exact for unitary links;
        the self-test compares with the direct products). All R at once: few, large GPU launches."""
        o, xp, ell = self.ops, self.ops.xp, self.box.ell
        perm = (0, 1 + i, 1 + j, 1 + k, 1 + l)
        cut = slice(0, ell + 1)
        Vi = xp.transpose(U[i], perm + tuple(range(5, U[i].ndim)))[:, :ell + 1, :ell + 1, cut, cut]
        Vj = xp.transpose(U[j], perm + tuple(range(5, U[j].ndim)))[:, :ell + 1, :ell + 1, cut, cut]
        one = xp.zeros_like(Vi[:, 0])
        if o.group == "su2":
            one[..., 0] = 1.0
        Pi, Pj = [one], [one]
        for x in range(ell):
            Pi.append(o.mul(Pi[-1], Vi[:, x]))
            Pj.append(o.mul(Pj[-1], Vj[:, :, x]))
        Pi = xp.stack(Pi, axis=1)  # (B, x, y, k, l): product of Vi(0..x-1, y)
        Pj = xp.stack(Pj, axis=2)  # (B, x, y, k, l): product of Vj(x, 0..y-1)
        Rs = np.arange(1, ell + 1)
        aR = xp.asarray((ell - Rs) // 2)
        bR = xp.asarray((ell - Rs) // 2 + Rs)
        bottom = o.mul(o.dag(Pi[:, aR, aR]), Pi[:, bR, aR])
        right = o.mul(o.dag(Pj[:, bR, aR]), Pj[:, bR, bR])
        top = o.mul(o.dag(Pi[:, aR, bR]), Pi[:, bR, bR])
        left = o.mul(o.dag(Pj[:, aR, aR]), Pj[:, aR, bR])
        W = o.mul(o.mul(bottom, right), o.mul(o.dag(top), o.dag(left)))
        re = o.re(W).reshape(self.B, ell, -1) @ self.oh2
        im = o.im(W)
        return re, (im.reshape(self.B, ell, -1) @ self.oh2 if im is not None else None)

    def centred_loops_direct(self, U, i, j, k, l):
        """The same by direct products (slow; for the self-test)."""
        o, xp, ell = self.ops, self.ops.xp, self.box.ell
        perm = (0, 1 + i, 1 + j, 1 + k, 1 + l)
        cut = slice(0, ell + 1)
        Vi = xp.transpose(U[i], perm + tuple(range(5, U[i].ndim)))
        Vj = xp.transpose(U[j], perm + tuple(range(5, U[j].ndim)))
        re, im = [], []
        for R in range(1, ell + 1):
            a = (ell - R) // 2

            def line_i(y):
                out = Vi[:, a, y, cut, cut]
                for x in range(a + 1, a + R):
                    out = o.mul(out, Vi[:, x, y, cut, cut])
                return out

            def line_j(x):
                out = Vj[:, x, a, cut, cut]
                for y in range(a + 1, a + R):
                    out = o.mul(out, Vj[:, x, y, cut, cut])
                return out

            W = o.mul(o.mul(line_i(a), line_j(a + R)), o.mul(o.dag(line_i(a + R)), o.dag(line_j(a))))
            re.append(o.re(W).reshape(self.B, -1) @ self.oh2)
            if o.im(W) is not None:
                im.append(o.im(W).reshape(self.B, -1) @ self.oh2)
        return xp.stack(re, axis=1), (xp.stack(im, axis=1) if im else None)

    def lines(self, U):
        o, ell = self.ops, self.box.ell
        cut = slice(0, ell + 1)
        L = U[0][:, 0, cut, cut, cut]
        for x in range(1, ell):
            L = o.mul(L, U[0][:, x, cut, cut, cut])
        return o.re(L).reshape(self.B, -1) @ self.oh3

    def __call__(self, U):
        o, xp = self.ops, self.ops.xp
        res = {}
        P = self.plaquettes(U)
        plaq, adm = [], xp.zeros((self.B, len(EPS), self.nd))
        for k, p in enumerate(P):
            v = o.re(p)
            plaq.append(self._binned(k, v) / xp.asarray(np.maximum(self.pcount[k], 1)))
            for e, eps in enumerate(EPS):
                adm[:, e] += self._binned(k, (1.0 - v > eps).astype(float))
        res["plaq"] = xp.stack(plaq, axis=1)
        res["adm"] = adm
        if o.group == "u1":
            res["sinp"] = self._binned(0, o.im(P[0])) / xp.asarray(np.maximum(self.pcount[0], 1))
        res["loops"], im = self.centred_loops(U, 0, 1, 2, 3)
        if im is not None:
            res["loops_im"] = im
        res["ctrl"], _ = self.centred_loops(U, 2, 3, 0, 1)
        if self.smear:
            res["loops_s"], im = self.centred_loops(self.smear_plane(U, 0, 1), 0, 1, 2, 3)
            if im is not None:
                res["loops_s_im"] = im
            res["ctrl_s"], _ = self.centred_loops(self.smear_plane(U, 2, 3), 2, 3, 0, 1)
        res["lines"] = self.lines(U)
        return {k: to_host(v) for k, v in res.items()}

    def periodic(self, U):
        """Whole periodic lattice: mean plaquette (B,) and admissibility fractions (B, 3)."""
        o, xp = self.ops, self.ops.xp
        P = [o.re(p).reshape(self.B, -1) for p in self.plaquettes(U)]
        P = xp.concatenate(P, axis=1)
        frac = xp.stack([(1.0 - P > e).mean(axis=1) for e in EPS], axis=1)
        return to_host(P.mean(axis=1)), to_host(frac)


# ---------------------------------------------------------------------------------------------------------------------------- run

def make_updater(group, box, beta, U, seed, gpu, pairs=False, icdf=False):
    """icdf: inverse-CDF heat bath (continuous coupling for paired chains); SU(2) then uses the array-code path, also on the GPU."""
    if group == "su2":
        if icdf:
            return CPUSU2(box, beta, U, seed, pairs, xp=get_xp(gpu), icdf=True)
        return GPUSU2(box, beta, U, seed, pairs) if gpu else CPUSU2(box, beta, U, seed, pairs)
    return U1Updater(get_xp(gpu), box, beta, U, seed, z2=(group == "z2"), pairs=pairs, icdf=icdf)


def make_ops(group, xp):
    return SU2Ops(xp) if group == "su2" else U1Ops(xp)


def run(a):
    gpu = not a.cpu
    xp = get_xp(gpu)
    box = Box(a.ell)
    B = a.chains
    ops = make_ops(a.group, xp)
    U0 = initial_links(a.group, box, a.bc, B, a.seed, a.phi)
    upd = make_updater(a.group, box, a.beta, U0, a.seed, gpu)
    meas = Measure(ops, box, B, smear=a.smear)
    t0 = time.time()
    per_plaq, per_adm = [], []
    if a.bc == "typical":
        alldyn = [np.ones(box.dims, bool)] * 4
        upd.set_dynamic(alldyn)
        for _ in range(a.periodic_therm):
            upd.sweep(a.n_or)
        for _ in range(a.periodic_meas):
            for _ in range(a.every):
                upd.sweep(a.n_or)
            p, f = meas.periodic(upd.links())
            per_plaq.append(p)
            per_adm.append(f)
        upd.set_dynamic(box.dyn)
        print(f"periodic stage done: plaq {np.mean(per_plaq):.5f} t={time.time() - t0:.0f}s", flush=True)
    frozen0 = [to_host(u)[:, ~box.dyn[mu]].copy() for mu, u in enumerate(upd.links())]
    for _ in range(a.n_therm):
        upd.sweep(a.n_or)
    rec = {}

    def save(m, partial):
        drift = max(float(np.max(np.abs(to_host(u)[:, ~box.dyn[mu]] - frozen0[mu]))) for mu, u in enumerate(upd.links()))
        np.savez(a.out, group=a.group, beta=a.beta, ell=a.ell, N=box.N, bc=a.bc, seed=a.seed, chains=B, n_therm=a.n_therm,
                 n_or=a.n_or, every=a.every, phi=DEFAULT_PHI[a.group] if a.phi is None else a.phi, smear=a.smear, eps=np.array(EPS), backend="gpu" if gpu else "cpu",
                 pcount=meas.pcount, count2=meas.count2, count3=meas.count3,
                 periodic_plaq=np.array(per_plaq), periodic_adm=np.array(per_adm), frozen_drift=drift,
                 seconds=time.time() - t0, partial=int(partial), n_done=m,
                 **{k: np.array(v[:m]) for k, v in rec.items()})
        return drift

    for m in range(a.n_meas):
        for _ in range(a.every):
            upd.sweep(a.n_or)
        r = meas(upd.links())
        for k, v in r.items():
            rec.setdefault(k, []).append(v)
        if m % 100 == 0:
            if m:
                save(m, True)
            pl = np.mean(rec["plaq"][-1][:, :, -1])
            print(f"{a.group} beta={a.beta} ell={a.ell} bc={a.bc} meas {m}/{a.n_meas} plaq(centre)={pl:.5f} "
                  f"t={time.time() - t0:.0f}s", flush=True)
    drift = save(a.n_meas, False)
    print(f"done {a.out} frozen drift {drift:.1e} in {time.time() - t0:.0f}s", flush=True)
    if drift != 0.0:
        print("FROZEN LINKS CHANGED: FAIL")
        return 1
    return 0


# ---------------------------------------------------------------------------------------------------------------------------- coupled

def shell_mask(box):
    """Shell links (BLUEPRINT-REDUCTION.md: the boundary dV of the dynamic link set V): frozen links that share a plaquette with a
    dynamic link. List of 4 bool arrays."""
    shell = [np.zeros(box.dims, bool) for _ in range(4)]
    for mu in range(4):
        D = box.dyn[mu]
        for nu in range(4):
            if nu == mu:
                continue
            shell[nu] |= np.roll(D, 1, axis=mu) | D | np.roll(np.roll(D, 1, axis=mu), -1, axis=nu) | np.roll(D, -1, axis=nu)
            shell[mu] |= np.roll(D, 1, axis=nu) | np.roll(D, -1, axis=nu)
    return [sh_ & ~d for sh_, d in zip(shell, box.dyn)]


def shell_link(box, kind):
    """A representative shell link (direction 1, in the face x = 0): 'face' at the face centre, 'edge' next to an edge of the face,
    'corner' next to a corner. Returns (mu, site)."""
    c = box.ell // 2
    site = {"face": (0, c, c, c), "edge": (0, c, 1, c), "corner": (0, 1, 1, 1)}[kind]
    return 1, site


def perturb(group, U, y, theta):
    """Change the shell link y = (mu, site) in the odd chains: SU(2) times exp(i theta sigma_3), U(1) + theta, Z2 flipped (theta = pi).
    Returns U (modified in place)."""
    mu, site = y
    idx = (slice(1, None, 2),) + tuple(site)
    if group == "su2":
        U[mu][idx] = qmul(U[mu][idx], np.array([np.cos(theta), 0.0, 0.0, np.sin(theta)]))
    elif group == "z2":
        U[mu][idx] = np.pi - U[mu][idx]
    else:
        U[mu][idx] = U[mu][idx] + theta
    return U


def link_dist(ops, a, b):
    """Bi-invariant distance of two links: SU(2) the angle on S^3, arccos((a b^dagger)_0) in [0, pi]; U(1), Z2 |angle difference|."""
    xp = ops.xp
    if ops.group == "su2":
        q = ops.mul(a, ops.dag(b))
        return xp.arctan2(xp.linalg.norm(q[..., 1:], axis=-1), q[..., 0])  # = arccos(q_0), accurate near 0
    return xp.abs(xp.angle(xp.exp(1j * (a - b))))


class Aligner:
    """Relative Landau gauge: transform the odd chain of each pair by interior gauge transformations k so that sum_e Re tr(U_e U''_e^dagger)
    is maximal (U the even chain, U'' = k U' k^dagger); checkerboard site updates with overrelaxation omega (Z2: plain maximisation).
    Works on a copy; any k gives an upper estimate of the coupling distance, so imperfect convergence errs on the safe side."""

    def __init__(self, ops, box, z2=False, omega=1.7):
        self.ops, self.box, self.z2, self.omega = ops, box, z2, omega
        xp = ops.xp
        extra = (1,) if ops.group == "su2" else ()
        self.masks = [xp.asarray((box.interior & box.parity[p]).reshape((1,) + box.dims + extra)) for p in (0, 1)]

    def functional(self, U, V):
        o = self.ops
        return sum(o.re(o.mul(U[mu], o.dag(V[mu]))).sum(axis=(1, 2, 3, 4)) for mu in range(4))

    def __call__(self, U, V, n_iter=300, tol=1e-12):
        """Iterate until the largest gauge rotation of a sweep is below tol (radians) or n_iter sweeps."""
        o, xp = self.ops, self.ops.xp
        V = [v.copy() for v in V]
        it = 0
        for it in range(1, n_iter + 1):
            biggest = 0.0
            for p in (0, 1):
                M = 0
                for mu in range(4):
                    M = M + o.mul(V[mu], o.dag(U[mu])) + sh(o.mul(o.dag(V[mu]), U[mu]), mu, -1)
                if o.group == "su2":
                    g = o.dag(M / xp.maximum(xp.linalg.norm(M, axis=-1, keepdims=True), 1e-300))
                    if not self.z2 and self.omega != 1.0:  # overrelaxation g -> g^omega
                        nv = xp.linalg.norm(g[..., 1:], axis=-1, keepdims=True)
                        ang = xp.arctan2(nv, g[..., :1])
                        vec = g[..., 1:] / xp.maximum(nv, 1e-300)
                        g = xp.concatenate([xp.cos(self.omega * ang), xp.sin(self.omega * ang) * vec], axis=-1)
                    one = xp.zeros_like(g)
                    one[..., 0] = 1.0
                    g = xp.where(self.masks[p], g, one)
                    biggest = max(biggest, float(xp.max(xp.linalg.norm(g[..., 1:], axis=-1))))
                else:
                    Mc = 0
                    for mu in range(4):
                        Mc = Mc + xp.exp(1j * (V[mu] - U[mu])) + sh(xp.exp(1j * (U[mu] - V[mu])), mu, -1)
                    if self.z2:
                        g = xp.where(Mc.real >= 0, 0.0, np.pi)
                    else:
                        g = -self.omega * xp.angle(Mc)
                    g = xp.where(self.masks[p], g, 0.0)
                    biggest = max(biggest, float(xp.max(xp.abs(xp.angle(xp.exp(1j * g))))))
                V = [o.mul(o.mul(g, V[mu]), o.dag(sh(g, mu))) for mu in range(4)]
            if biggest < tol:
                break
        return V, it


def couple(a):
    """Coupled-chain upper estimate of k_V(y) (BLUEPRINT-REDUCTION.md section 5.1): pairs of chains with boundary conditions that differ
    only at the shell link y, synchronous coupling (shared random numbers), relative Landau alignment, distance sum_e rho(U_e, U'_e) /
    rho(tau_y, tau'_y). Also records the ordinary observables of both chains (witnesses: their differences are lower bounds)."""
    gpu = not a.cpu
    xp = get_xp(gpu)
    box = Box(a.ell)
    B = 2 * a.pairs
    ops = make_ops(a.group, xp)
    theta = np.pi if a.group == "z2" else a.theta
    y = shell_link(box, a.y)
    t0 = time.time()
    U0 = initial_links(a.group, box, a.bc, B, a.seed, a.phi)
    for mu in range(4):
        U0[mu][1::2] = U0[mu][0::2]
    upd = make_updater(a.group, box, a.beta, U0, a.seed, gpu, pairs=True, icdf=True)
    if a.bc == "typical":
        upd.set_dynamic([np.ones(box.dims, bool)] * 4)
        for _ in range(a.periodic_therm):
            upd.sweep(a.n_or)
        upd.set_dynamic(box.dyn)
    for _ in range(a.n_therm):
        upd.sweep(a.n_or)
    U = [to_host(u).copy() for u in upd.links()]
    same = max(float(np.max(np.abs(u[0::2] - u[1::2]))) for u in U)
    U = perturb(a.group, U, y, theta)
    upd = make_updater(a.group, box, a.beta, U, a.seed + 1, gpu, pairs=True, icdf=True)
    al = Aligner(ops, box, z2=(a.group == "z2"))
    meas = Measure(ops, box, B, smear=a.smear)
    # link bins: depth (min over the two ends) and Chebyshev distance of the link midpoint from y's midpoint
    idx = np.indices(box.dims).astype(float)
    ymid = np.array(y[1], float)
    ymid[y[0]] += 0.5
    depth_bins, ry_bins = [], []
    for mu in range(4):
        dmu = np.minimum(box.sdepth, roll_np(box.sdepth, mu))
        mid = idx.copy()
        mid[mu] += 0.5
        ry = np.floor(np.max(np.abs(mid - ymid[:, None, None, None, None]), axis=0)).astype(int)
        depth_bins.append(np.where(box.dyn[mu], dmu, -1))
        ry_bins.append(np.where(box.dyn[mu], ry, -1))
    nd = max(int(d.max()) for d in depth_bins) + 1
    nr = max(int(r.max()) for r in ry_bins) + 1
    oh_d = [xp.asarray(np.eye(nd + 1)[np.where(d >= 0, d, nd).reshape(-1)][:, :nd]) for d in depth_bins]
    oh_r = [xp.asarray(np.eye(nr + 1)[np.where(r >= 0, r, nr).reshape(-1)][:, :nr]) for r in ry_bins]
    dynx = [xp.asarray(d.reshape((1,) + box.dims)) for d in box.dyn]
    shell = shell_mask(box)
    rec = {}

    def save(m, partial):
        np.savez(a.out, mode="couple", group=a.group, beta=a.beta, ell=a.ell, N=box.N, bc=a.bc, seed=a.seed, pairs=a.pairs,
                 chains=B, y_kind=a.y, y_mu=y[0], y_site=np.array(y[1]), theta=theta, n_therm=a.n_therm, n_or=a.n_or, every=a.every,
                 couple_or=a.couple_or, realign=int(not a.no_realign),
                 phi=DEFAULT_PHI[a.group] if a.phi is None else a.phi, smear=a.smear, n_dynamic=box.n_dynamic(),
                 n_shell=int(sum(x.sum() for x in shell)), start_pair_diff=same, eps=np.array(EPS),
                 pcount=meas.pcount, count2=meas.count2, count3=meas.count3, seconds=time.time() - t0, partial=int(partial),
                 n_done=m, **{k: np.array(v[:m]) for k, v in rec.items()})

    def coupled_sweep():
        """Pure heat bath (overrelaxation is an isometry and never forgets a difference), then, unless --no-realign, the odd chain of
        each pair is gauge-aligned to the even one on the running state. Interior gauge transformations leave the law of every
        gauge-invariant observable unchanged, and the shared-random-number update is not gauge covariant in SU(2): without this, the
        relative gauge of a pair drifts and the drift turns into physical differences."""
        upd.sweep(a.couple_or)
        if not a.no_realign:
            L = upd.links()
            Ua, _ = al([u[0::2] for u in L], [u[1::2] for u in L], a.align_iter)
            for mu in range(4):
                upd.U[mu][1::2] = Ua[mu]

    for m in range(a.n_meas):
        for _ in range(a.every):
            coupled_sweep()
        L = upd.links()
        Ue = [u[0::2] for u in L]
        Uo = [u[1::2] for u in L]
        Ua, it = al(Ue, Uo, a.align_iter)
        tot, byd, byr, dis = 0, 0, 0, 0
        raw = 0
        for mu in range(4):
            dm = link_dist(ops, Ue[mu], Ua[mu]) * dynx[mu]
            raw = raw + (link_dist(ops, Ue[mu], Uo[mu]) * dynx[mu]).sum(axis=(1, 2, 3, 4))
            tot = tot + dm.sum(axis=(1, 2, 3, 4))
            flat = dm.reshape(a.pairs, -1)
            byd = byd + flat @ oh_d[mu]
            byr = byr + flat @ oh_r[mu]
            dis = dis + ((dm > 1e-8) & dynx[mu]).sum(axis=(1, 2, 3, 4))
        r = {"k_hat": to_host(tot) / theta, "k_raw": to_host(raw) / theta, "dist_depth": to_host(byd) / theta,
             "dist_ry": to_host(byr) / theta, "n_disagree": to_host(dis), "align_iter": np.full(a.pairs, it)}
        r.update(meas(L))
        for k, v in r.items():
            rec.setdefault(k, []).append(v)
        if m % 50 == 0:
            if m:
                save(m, True)
            print(f"couple {a.group} beta={a.beta} ell={a.ell} bc={a.bc} y={a.y} meas {m}/{a.n_meas} k_hat={np.mean(r['k_hat']):.3f} "
                  f"(unaligned {np.mean(r['k_raw']):.3f}, align iters {it}) t={time.time() - t0:.0f}s", flush=True)
    save(a.n_meas, False)
    print(f"done {a.out} in {time.time() - t0:.0f}s", flush=True)
    return 0


# ---------------------------------------------------------------------------------------------------------------------------- tests

def ks_pvalue(samples, cdf):
    """One-sample Kolmogorov-Smirnov test against a tabulated cdf (callable)."""
    x = np.sort(samples)
    n = x.size
    F = cdf(x)
    D = max(np.max(np.arange(1, n + 1) / n - F), np.max(F - np.arange(n) / n))
    lam = (np.sqrt(n) + 0.12 + 0.11 / np.sqrt(n)) * D
    k = np.arange(1, 101)
    return D, float(np.clip(2 * np.sum((-1) ** (k - 1) * np.exp(-2 * k * k * lam * lam)), 0, 1))


def tab_cdf(xs, dens):
    c = np.concatenate([[0.0], np.cumsum(0.5 * (dens[1:] + dens[:-1]) * np.diff(xs))])
    c /= c[-1]
    return lambda x: np.interp(x, xs, c)


def random_gauge(group, box, B, rng):
    """Random gauge transformation on the interior sites (identity elsewhere)."""
    n = (B,) + box.dims
    if group == "su2":
        g = rng.normal(size=n + (4,))
        g /= np.linalg.norm(g, axis=-1, keepdims=True)
        g[:, ~box.interior] = [1.0, 0, 0, 0]
    elif group == "z2":
        g = np.pi * rng.integers(0, 2, size=n).astype(float)
        g[:, ~box.interior] = 0.0
    else:
        g = rng.uniform(-np.pi, np.pi, size=n)
        g[:, ~box.interior] = 0.0
    return g


def gauge_transform(ops, U, g):
    return [ops.mul(ops.mul(g, U[mu]), ops.dag(sh(g, mu))) for mu in range(4)]


def selftest(a):
    gpu = a.gpu
    ok = True

    def report(name, good, detail):
        nonlocal ok
        ok &= bool(good)
        print(f"{'PASS' if good else 'FAIL'}  {name}: {detail}", flush=True)

    rng = np.random.default_rng(5)
    # 1. staples equal those of the unconstrained reference code (su2.py, u1.py) on a random periodic configuration
    sys.path.insert(0, HERE)
    from su2 import Lattice
    from u1 import U1Lattice
    box = Box(2)  # N = 4
    q = rng.normal(size=(4, 1) + box.dims + (4,))
    q /= np.linalg.norm(q, axis=-1, keepdims=True)
    lat = Lattice(4, 4, 2.3, 0)
    lat.U = q[:, 0].copy()
    worst = max(np.max(np.abs(staple_generic(SU2Ops(np), list(q), mu)[0] - lat.staple(mu))) for mu in range(4))
    th = rng.uniform(-np.pi, np.pi, size=(4, 1) + box.dims)
    ul = U1Lattice(4, 4, 1.0, 0)
    ul.th = th[:, 0].copy()
    worst_u1 = max(np.max(np.abs(staple_generic(U1Ops(np), list(th), mu)[0] - ul.staple(mu))) for mu in range(4))
    report("staple = reference code (su2.py, u1.py)", max(worst, worst_u1) < 1e-12, f"max diff {worst:.1e} / {worst_u1:.1e}")

    # 2. frozen links never change; dynamic links do (CPU paths, and GPU paths with --gpu)
    BT = {"su2": 2.3, "u1": 1.0, "z2": 0.3}
    paths = [("su2", False), ("u1", False), ("z2", False)] + ([("su2", True), ("u1", True), ("z2", True)] if gpu else [])
    for group, g_ in paths:
        box = Box(4)
        for bc in (("hot", "twist") if group == "z2" else ("hot", "twist", "flux")):
            U0 = initial_links(group, box, bc, 2, 3)
            upd = make_updater(group, box, BT[group], U0, 3, g_)
            for _ in range(3):
                upd.sweep(2)
            L = [to_host(u) for u in upd.links()]
            fz = max(float(np.max(np.abs(L[mu][:, ~box.dyn[mu]] - U0[mu][:, ~box.dyn[mu]]))) for mu in range(4))
            dy = min(float(np.max(np.abs(L[mu][:, box.dyn[mu]] - U0[mu][:, box.dyn[mu]]))) for mu in range(4))
            report(f"frozen links unchanged ({group}, {'gpu' if g_ else 'cpu'}, {bc})", fz == 0.0 and dy > 1e-3,
                   f"frozen max change {fz:.1e}, dynamic min-over-directions max change {dy:.2f}")

    # 2b. synchronous coupling: paired chains with identical starts stay identical; a pair that differs at one shell link separates
    for group, g_ in paths:
        box = Box(4)
        U0 = initial_links(group, box, "hot", 4, 7)
        for mu in range(4):
            U0[mu][1::2] = U0[mu][0::2]
        y = shell_link(box, "face")
        U1 = perturb(group, [u.copy() for u in U0], y, 0.5)
        res = []
        for start in (U0, U1):
            upd = make_updater(group, box, BT[group], start, 8, g_, pairs=True, icdf=True)
            for _ in range(4):
                upd.sweep(2)
            L = [to_host(u) for u in upd.links()]
            res.append(max(float(np.max(np.abs(L[mu][0::2] - L[mu][1::2]))) for mu in range(4)))
        tol = 1e-12 if not (g_ and group == "su2") else 1e-9
        report(f"paired chains share their random numbers ({group}, {'gpu' if g_ else 'cpu'})", res[0] < tol and res[1] > 1e-6,
               f"identical starts: max link difference {res[0]:.1e}; one shell link changed: {res[1]:.2e}")

    # 2c. relative Landau alignment recovers a gauge copy (SU(2), U(1): a full random interior gauge transformation; Z2: 10 % of the
    #     interior sites flipped; a greedy Z2 alignment can stall in domains far from the optimum, which only overestimates k)
    for group, frac in (("su2", 1.0), ("u1", 1.0), ("z2", 0.1)):
        box = Box(6)
        ops = make_ops(group, np)
        upd = make_updater(group, box, BT[group], initial_links(group, box, "calm", 2, 41), 41, False)
        for _ in range(10):
            upd.sweep(2)
        U = [np.array(u) for u in upd.links()]
        g = random_gauge(group, box, 2, rng)
        keep = rng.random(g.shape[:5]) > frac
        g[keep] = [1.0, 0, 0, 0] if group == "su2" else 0.0
        V = gauge_transform(ops, U, g)
        Va, it = Aligner(ops, box, z2=(group == "z2"))(U, V, 3000)
        d0 = sum(float((link_dist(ops, U[m], V[m]) * box.dyn[m]).sum()) for m in range(4))
        d1 = sum(float((link_dist(ops, U[m], Va[m]) * box.dyn[m]).sum()) for m in range(4))
        report(f"relative Landau alignment recovers a gauge copy ({group})", d1 < 1e-6,
               f"summed link distance {d0:.0f} -> {d1:.1e} in {it} sweeps")

    # 3. heat bath exact for a link whose neighbours are frozen at random values: one dynamic link, samples vs exact density
    cases = [(gr, g_, b, False) for gr, g_ in paths for b in ({"su2": (0.1, 2.3), "u1": (1.0, 4.0), "z2": (0.3, 0.6)}[gr])]
    cases += [("su2", g_, 2.3, True) for g_ in sorted({p[1] for p in paths})] + [("u1", g_, 4.0, True) for g_ in sorted({p[1] for p in paths})]
    for group, g_, beta, icdf in cases:
        box = Box(2)
        B = 400
        for env_seed in range(12, 60):  # Z2: pick an environment whose staple does not vanish
            U0 = initial_links(group, box, "hot", B, 11)
            # make every link random and frozen, then let exactly one link move
            r = np.random.default_rng(env_seed)
            for mu in range(4):
                if group == "su2":
                    x = r.normal(size=U0[mu].shape)
                    U0[mu] = x / np.linalg.norm(x, axis=-1, keepdims=True)
                    U0[mu][:] = U0[mu][:1]  # same frozen environment in every chain
                elif group == "z2":
                    U0[mu] = np.broadcast_to(np.pi * r.integers(0, 2, size=(1,) + box.dims), U0[mu].shape).astype(float)
                else:
                    U0[mu] = np.broadcast_to(r.uniform(-np.pi, np.pi, size=(1,) + box.dims), U0[mu].shape).copy()
            one = [np.zeros(box.dims, bool) for _ in range(4)]
            site = (0, 1, 1, 1)
            one[0][site] = True
            upd = make_updater(group, box, beta, U0, 13, g_, icdf=icdf)
            upd.set_dynamic(one)
            ops = make_ops(group, np)
            A = staple_generic(ops, [to_host(u) for u in upd.links()], 0)[0][site]
            if group != "z2" or abs(A.real) >= 2:
                break
        samples = []
        for _ in range(50):
            upd.sweep(0)
            u = to_host(upd.links()[0])[:, site[0], site[1], site[2], site[3]]
            if group == "su2":
                k = np.linalg.norm(A)
                samples.append(qmul(u, A[None, :] / k)[:, 0])
            elif group == "z2":
                samples.append(u.copy())  # u is a view of the live links
            else:
                k = abs(A)
                samples.append(np.angle(np.exp(1j * (u + np.angle(A)))))
        s_ = np.concatenate(samples)
        if group == "z2":
            p0 = 1 / (1 + np.exp(-2 * beta * A.real))
            f0 = np.mean(np.cos(s_) > 0)  # fraction with theta = 0; exact P(theta = 0) = 1 / (1 + exp(-2 beta Re A))
            z = (f0 - p0) / np.sqrt(p0 * (1 - p0) / s_.size)
            report(f"heat bath exact, one link in a frozen random environment ({group}, {'gpu' if g_ else 'cpu'}, beta {beta})",
                   abs(z) < 4, f"Re A = {A.real:+.0f}, P(theta = 0) measured {f0:.4f} vs exact {p0:.4f} (z = {z:+.2f})")
            continue
        if group == "su2":
            xs = np.linspace(-1, 1, 40001)
            cdf = tab_cdf(xs, np.sqrt(np.maximum(1 - xs * xs, 0)) * np.exp(beta * k * (xs - 1)))
        else:
            xs = np.linspace(-np.pi, np.pi, 40001)
            cdf = tab_cdf(xs, np.exp(beta * k * (np.cos(xs) - 1)))
        D, p = ks_pvalue(s_, cdf)
        # overrelaxation keeps the local action exactly
        before = to_host(upd.links()[0])[:, site[0], site[1], site[2], site[3]].copy()
        upd.overrelax()
        after = to_host(upd.links()[0])[:, site[0], site[1], site[2], site[3]]
        if group == "su2":
            dact = np.max(np.abs(qmul(after, A[None, :])[:, 0] - qmul(before, A[None, :])[:, 0]))
        else:
            dact = np.max(np.abs(np.cos(after + np.angle(A)) - np.cos(before + np.angle(A))))
        report(f"heat bath exact, one link in a frozen random environment ({group}, {'gpu' if g_ else 'cpu'}, beta {beta}"
               f"{', inverse CDF' if icdf else ''})", p > 0.01 and dact < 1e-10, f"beta*k = {beta * k:.2f}, {s_.size} samples, KS D = {D:.4f}, p = {p:.2f}; "
                                          f"overrelaxation changes the local action by {dact:.1e}")

    # 4. gauge invariance of every observable under a random interior gauge transformation
    for group in ("su2", "u1", "z2"):
        for ell in (5, 6):
            box = Box(ell)
            B = 2
            ops = make_ops(group, np)
            U0 = initial_links(group, box, "twist", B, 21)
            upd = make_updater(group, box, BT[group], U0, 21, False)
            for _ in range(3):
                upd.sweep(1)
            U = [np.array(u) for u in upd.links()]
            m = Measure(ops, box, B, smear=3)
            r1 = m(U)
            fast, slow = m.centred_loops(U, 0, 1, 2, 3), m.centred_loops_direct(U, 0, 1, 2, 3)
            dd = max(float(np.max(np.abs(f - s2))) for f, s2 in zip(fast, slow) if f is not None)
            report(f"centred loops: prefix products = direct products ({group}, ell={ell})", dd < 1e-12, f"max diff {dd:.1e}")
            Ug = gauge_transform(ops, U, random_gauge(group, box, B, rng))
            fz = max(float(np.max(np.abs(Ug[mu][:, ~box.dyn[mu]] - U[mu][:, ~box.dyn[mu]]))) for mu in range(4))
            r2 = m(Ug)
            worst = max(float(np.max(np.abs(r1[k] - r2[k]))) for k in r1 if k != "adm")
            admiss_same = np.array_equal(r1["adm"], r2["adm"])
            moved = max(float(np.max(np.abs(Ug[mu] - U[mu]))) for mu in range(4))
            report(f"gauge invariance ({group}, ell={ell}, twist BC)", worst < 1e-12 and fz < 1e-14 and moved > 0.1,
                   f"largest change of an observable {worst:.1e} (links moved by up to {moved:.2f}; frozen links {fz:.0e}; "
                   f"admissibility counts {'identical' if admiss_same else 'differ'})")

    # 5. the BCs: the boundary loop around a flux-plane cross-section, and the centred loops of the starting field
    for group in ("su2", "u1", "z2"):
        box = Box(6)
        ops = make_ops(group, np)
        m = Measure(ops, box, 1, smear=2)
        for bc in (("calm", "twist") if group == "z2" else ("calm", "flux", "twist")):
            r = m(initial_links(group, box, bc, 1, 0))
            edge = np.concatenate([r["loops"][0, -1, 1:], r["loops_s"][0, -1, 1:]])
            want = 1.0 if (bc == "calm" or group == "u1") else -1.0
            report(f"boundary holonomy of a cross-section ({group}, {bc})", np.allclose(edge, want, atol=1e-12),
                   f"loop R = ell at every slice = {edge.mean():+.6f} (expected {want:+.0f}); mean flux-plane plaquette at depth 0 "
                   f"(dynamic ones) {r['plaq'][0, 0, 0]:.4f}")

    # 6. GPU path: quaternion <-> matrix conversion and plaquette against the kernel's own plaquette
    if gpu:
        import cupy as cp
        box = Box(6)
        U0 = initial_links("su2", box, "hot", 2, 4)
        upd = GPUSU2(box, 2.3, U0, 4)
        for _ in range(3):
            upd.sweep(2)
        Q = upd.links()
        back = max(float(cp.max(cp.abs(q2m(Q[mu], cp) - upd.g.U[mu]))) for mu in range(4))
        ker = upd.g.plaquette(per_site=True)  # sum over the 6 planes of (1/2) Re tr, per site
        mine = sum(SU2Ops(cp).re(p) for p in Measure(SU2Ops(cp), box, 2).plaquettes(Q))
        d = float(cp.max(cp.abs(ker - mine)))
        report("GPU: matrix <-> quaternion and plaquette vs kernel", back < 1e-14 and d < 1e-12, f"round trip {back:.1e}, plaquette {d:.1e}")

    # 7. bulk (indicative, statistical): the box interior with a typical boundary has the periodic plaquette
    box = Box(6)
    B = 4
    U0 = initial_links("su2", box, "calm", B, 31)
    upd = make_updater("su2", box, 2.3, U0, 31, gpu)
    upd.set_dynamic([np.ones(box.dims, bool)] * 4)
    ops = SU2Ops(get_xp(gpu))
    m = Measure(ops, box, B)
    for _ in range(60):
        upd.sweep(3)
    per = []
    for _ in range(40):
        upd.sweep(3)
        per.append(m.periodic(upd.links())[0])
    upd.set_dynamic(box.dyn)
    for _ in range(30):
        upd.sweep(3)
    deep = []
    for _ in range(60):
        upd.sweep(3)
        r = m(upd.links())
        deep.append((r["plaq"][:, :, -1] * m.pcount[:, -1]).sum(axis=1) / m.pcount[:, -1].sum())
    per, deep = np.array(per).mean(axis=0), np.array(deep).mean(axis=0)
    dlt = deep.mean() - per.mean()
    err = np.hypot(deep.std(ddof=1) / 2, per.std(ddof=1) / 2)
    report("bulk: deepest box plaquettes (typical BC) vs the periodic lattice, beta 2.3 (indicative)", abs(dlt) < 4 * err + 2e-3,
           f"periodic {per.mean():.4f}, box centre {deep.mean():.4f} (diff {dlt:+.4f} +- {err:.4f}; reference 0.6022 on 10^4)")

    print("SELFTEST", "OK" if ok else "FAILED")
    return 0 if ok else 1


def bench(a):
    import cupy as cp
    box = Box(6)  # N = 8
    out = []
    for B in (1, 8):
        U0 = initial_links("su2", box, "calm", B, 1)
        upd = GPUSU2(box, 2.4, U0, 1)
        meas = Measure(SU2Ops(cp), box, B)
        upd.sweep(3)
        cp.cuda.Device().synchronize()
        t = time.time()
        for _ in range(20):
            upd.sweep(3)
        cp.cuda.Device().synchronize()
        ts = (time.time() - t) / 20
        t = time.time()
        for _ in range(5):
            meas(upd.links())
        cp.cuda.Device().synchronize()
        tm = (time.time() - t) / 5
        free, total = cp.cuda.runtime.memGetInfo()
        sites = B * box.N ** 4
        out.append((B, ts, tm, sites))
        print(f"SU(2) ell=6 (N=8) chains={B}: sweep (1 HB + 3 OR) {ts * 1e3:.2f} ms = {ts / sites * 1e9:.0f} ns/site; measurement "
              f"{tm * 1e3:.1f} ms; GPU memory used by this process ~{cp.get_default_memory_pool().used_bytes() / 2**20:.0f} MiB")
    for B in (1, 8):
        U0 = initial_links("u1", box, "flux", B, 1)
        upd = U1Updater(cp, box, 1.1, U0, 1)
        upd.sweep(3)
        cp.cuda.Device().synchronize()
        t = time.time()
        for _ in range(5):
            upd.sweep(3)
        cp.cuda.Device().synchronize()
        ts = (time.time() - t) / 5
        print(f"U(1) ell=6 (N=8) chains={B}: sweep (1 HB + 3 OR) {ts * 1e3:.1f} ms = {ts / (B * box.N ** 4) * 1e9:.0f} ns/site")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("group", choices=("su2", "u1", "z2"))
    r.add_argument("beta", type=float)
    r.add_argument("ell", type=int)
    r.add_argument("bc", choices=("calm", "typical", "hot", "flux", "twist"))
    r.add_argument("n_therm", type=int)
    r.add_argument("n_meas", type=int)
    r.add_argument("seed", type=int)
    r.add_argument("out")
    r.add_argument("--chains", type=int, default=4)
    r.add_argument("--n-or", type=int, default=3)
    r.add_argument("--every", type=int, default=2)
    r.add_argument("--cpu", action="store_true")
    r.add_argument("--periodic-therm", type=int, default=300)
    r.add_argument("--periodic-meas", type=int, default=50)
    r.add_argument("--phi", type=float, default=None, help="flux through a cross-section in units of pi (default su2 1, u1 2, z2 1)")
    r.add_argument("--smear", type=int, default=0, help="APE steps (alpha 0.5) in the loop planes for loops_s / ctrl_s")
    c = sub.add_parser("couple")
    c.add_argument("group", choices=("su2", "u1", "z2"))
    c.add_argument("beta", type=float)
    c.add_argument("ell", type=int)
    c.add_argument("bc", choices=("calm", "typical", "hot", "flux", "twist"))
    c.add_argument("y", choices=("face", "edge", "corner"))
    c.add_argument("n_therm", type=int)
    c.add_argument("n_meas", type=int)
    c.add_argument("seed", type=int)
    c.add_argument("out")
    c.add_argument("--pairs", type=int, default=4)
    c.add_argument("--theta", type=float, default=0.5, help="size of the change of y (SU(2), U(1); Z2 always flips)")
    c.add_argument("--align-iter", type=int, default=300)
    c.add_argument("--n-or", type=int, default=3, help="overrelaxation steps per sweep while thermalising (before the change of y)")
    c.add_argument("--couple-or", type=int, default=0, help="overrelaxation steps per sweep of the coupled pair (default 0)")
    c.add_argument("--no-realign", action="store_true", help="do not gauge-align the pair on the running state")
    c.add_argument("--every", type=int, default=2)
    c.add_argument("--cpu", action="store_true")
    c.add_argument("--periodic-therm", type=int, default=300)
    c.add_argument("--phi", type=float, default=None)
    c.add_argument("--smear", type=int, default=0)
    s = sub.add_parser("selftest")
    s.add_argument("--gpu", action="store_true")
    sub.add_parser("bench")
    a = ap.parse_args()
    return {"run": run, "couple": couple, "selftest": selftest, "bench": bench}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
