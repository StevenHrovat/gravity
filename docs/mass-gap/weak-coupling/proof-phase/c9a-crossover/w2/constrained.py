"""W2 (c9a-crossover): the constrained box sampler and the coupled pairs of W2-PREREG.md, for timing and pipeline tests.

Box law (W2-PREREG.md section 2): SU(2) links based at the sites of a cube of side ELL (fine sites), given the frozen outside
links sigma and the block variables Y of the coarse links whose blurred path meets the box. Density, per box configuration U_B,

    exp( beta * sum_p (1/2) Re tr U_p )  *  prod_l exp( kappa <Y_l, Phi_l(U)> ) / z(kappa |Phi_l(U)|)

with Phi_l the UNPROJECTED good blocking of one doubling (straight 2-link path plus w times the six 2-link staples, a quaternion
sum), <a, b> = (1/2) Re tr(a^dag b) = a . b for quaternions, and z(a) = 2 I_1(a)/a the Haar-normalised SU(2) normaliser.
Every fine link enters every Phi_l at most once, so the exponent is linear in each link; the normaliser is not.

Update: per link, heat-bath proposal from exp(q . F), F = beta conj(Wilson staple) + kappa * (linear constraint field), then a
Metropolis step for the normaliser ratio (independence sampler; exact). Links are updated in 4 * 81 colour classes
(direction mu, x mod 3 in every direction): two links of one class share no plaquette and no blocking path.

Coupled pair (W2-PREREG.md section 3): two chains (boundary sigma / sigma^z, or Y / Y^l), coupled link by link by the maximal
coupling of the two proposals and a shared Metropolis uniform. Chain B is gauge-aligned to chain A at "free" sites (all eight
links dynamic, not a coarse site), an exact symmetry of its law. Disagreement = box links differing by more than TOL.

Quaternion layout and product as lattice/boundary.py (checked against gpu/gauge.py's 2x2 matrices: qmul <-> matrix product).

Usage
  py constrained.py selftest [--gpu]
  py constrained.py gen BETA NCONF SEED OUT.npz                       equilibrium 16^4 configurations (GPU, gpu/gauge.py)
  py constrained.py pilot CONF.npz BETA ELL KAPPA SWEEPS OUT.json [--pairs 4] [--every 10] [--gpu]
  py constrained.py job CONF.npz BETA ELL KAPPA YCLASS T OUT.json [--pool 8] [--batch 1] [--every 10] [--gpu]
"""

import argparse
import json
import math
import os
import sys
import time

sys.dont_write_bytecode = True
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
LAT = os.path.normpath(os.path.join(HERE, "..", "..", "..", "..", "lattice"))

W_STAPLE = 0.5
TOL = 1e-7
CONJ = np.array([1.0, -1.0, -1.0, -1.0])


# ====================================================================================================================== backend

class Backend:
    def __init__(self, gpu, seed):
        if gpu:
            import cupy as cp
            import cupyx.scipy.special as sps
            self.xp, self.i1e, self.i0e = cp, sps.i1e, sps.i0e
            self._qk = cp.ElementwiseKernel(
                "float64 a0, float64 a1, float64 a2, float64 a3, float64 b0, float64 b1, float64 b2, float64 b3",
                "float64 c0, float64 c1, float64 c2, float64 c3",
                "c0 = a0*b0 - a1*b1 - a2*b2 - a3*b3; c1 = a0*b1 + b0*a1 - (a2*b3 - a3*b2);"
                "c2 = a0*b2 + b0*a2 - (a3*b1 - a1*b3); c3 = a0*b3 + b0*a3 - (a1*b2 - a2*b1);", "qmul4")
            self.rng = cp.random.RandomState(seed)
        else:
            import scipy.special as sps
            self.xp, self.i1e, self.i0e = np, sps.i1e, sps.i0e
            self._qk = None
            self.rng = np.random.default_rng(seed)
        self.gpu = gpu
        self.conj = self.xp.asarray(CONJ)

    def uniform(self, shape):
        return self.rng.random_sample(shape) if self.gpu else self.rng.random(shape)

    def normal(self, shape):
        return self.rng.standard_normal(shape)

    def qmul(self, a, b):
        xp = self.xp
        if self._qk is not None:
            shape = np.broadcast_shapes(a.shape, b.shape)
            out = xp.empty(shape, dtype=xp.float64)
            self._qk(a[..., 0], a[..., 1], a[..., 2], a[..., 3], b[..., 0], b[..., 1], b[..., 2], b[..., 3],
                     out[..., 0], out[..., 1], out[..., 2], out[..., 3])
            return out
        a0, a1, a2, a3 = a[..., 0], a[..., 1], a[..., 2], a[..., 3]
        b0, b1, b2, b3 = b[..., 0], b[..., 1], b[..., 2], b[..., 3]
        return xp.stack([a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3,
                         a0 * b1 + b0 * a1 - (a2 * b3 - a3 * b2),
                         a0 * b2 + b0 * a2 - (a3 * b1 - a1 * b3),
                         a0 * b3 + b0 * a3 - (a1 * b2 - a2 * b1)], axis=-1)

    def dlog_z(self, a):
        """d/da log z(a) = I_0(a)/I_1(a) - 2/a (-> a/4 for small a)."""
        xp = self.xp
        a = xp.maximum(a, 1e-6)
        big = self.i0e(a) / self.i1e(a) - 2.0 / a
        return xp.where(a < 1e-3, a / 4.0, big)

    def log_z(self, a):
        """log z(a), z(a) = 2 I_1(a)/a (Haar-normalised SU(2) integral of exp(a <Y, n>)); z(0) = 1."""
        xp = self.xp
        a = xp.maximum(a, 1e-8)
        return math.log(2.0) + xp.log(self.i1e(a)) + a - xp.log(a)

    # ---------------------------------------------------------------- von Mises-Fisher on S^3 = SU(2): density ~ exp(q . F)
    def sample_x0(self, alpha, M=4):
        """x0 in [-1, 1] with density ~ sqrt(1 - x0^2) exp(alpha x0): Kennedy-Pendleton for alpha >= 0.3, else rejection.
        M candidates per pending element per round; the first accepted one is kept (exact: independent trials in order)."""
        xp = self.xp
        out = xp.zeros(alpha.shape)
        flat_a = alpha.reshape(-1)
        flat_o = out.reshape(-1)
        pend = xp.arange(flat_a.size)
        for _ in range(10000):
            if pend.size == 0:
                break
            a = flat_a[pend][None, :]
            big = a >= 0.3
            u = self.uniform((4, M, int(pend.size)))
            lam2 = -(xp.log(1.0 - u[0]) + xp.cos(2 * np.pi * u[1]) ** 2 * xp.log(1.0 - u[2])) / (2 * xp.maximum(a, 0.3))
            ok_kp = big & (u[3] ** 2 <= 1.0 - lam2)
            x_kp = 1.0 - 2.0 * lam2
            x_un = 2.0 * u[0] - 1.0
            ok_un = (~big) & (u[3] <= xp.sqrt(xp.maximum(0.0, 1.0 - x_un ** 2)) * xp.exp(a * (x_un - 1.0)))
            ok = ok_kp | ok_un
            x = xp.where(big, x_kp, x_un)
            anyok = ok.any(axis=0)
            first = xp.argmax(ok, axis=0)
            pick = x[first, xp.arange(x.shape[1])]
            flat_o[pend[anyok]] = pick[anyok]
            pend = pend[~anyok]
        else:
            raise RuntimeError("x0 sampler did not converge")
        return out

    def sample_vmf(self, F):
        """q ~ exp(q . F) on unit quaternions (F of shape (..., 4))."""
        xp = self.xp
        a = xp.linalg.norm(F, axis=-1)
        x0 = self.sample_x0(a)
        v = self.normal(F.shape[:-1] + (3,))
        v = v / xp.linalg.norm(v, axis=-1, keepdims=True)
        X = xp.concatenate([x0[..., None], v * xp.sqrt(xp.maximum(0.0, 1.0 - x0 * x0))[..., None]], axis=-1)
        n = F / xp.maximum(a, 1e-300)[..., None]
        n = xp.where((a > 1e-12)[..., None], n, xp.asarray([1.0, 0.0, 0.0, 0.0]))
        return self.qmul(X, n)

    def coupled_vmf(self, F1, F2):
        """Maximal coupling of exp(q . F1) and exp(q . F2): q1 ~ p1, q2 ~ p2, q1 = q2 with probability 1 - TV."""
        xp = self.xp
        q1 = self.sample_vmf(F1)
        a1, a2 = xp.linalg.norm(F1, axis=-1), xp.linalg.norm(F2, axis=-1)
        c = self.log_z(a1) - self.log_z(a2)
        L = xp.sum(q1 * (F2 - F1), axis=-1) + c
        acc = xp.log(xp.maximum(self.uniform(L.shape), 1e-300)) <= L
        q2 = q1.copy()
        flatq2 = q2.reshape(-1, 4)
        pend = xp.nonzero(~acc.reshape(-1))[0]
        if pend.size:
            f1 = F1.reshape(-1, 4)[pend]
            f2 = F2.reshape(-1, 4)[pend]
            cc = c.reshape(-1)[pend]
            amax = xp.maximum(1.0 - xp.exp(-xp.linalg.norm(f1 - f2, axis=-1) - cc), 1e-300)
            out = xp.zeros((pend.size, 4))
            loc = xp.arange(pend.size)
            Mc = 16                                         # candidates per pending element per round
            for _ in range(100000):
                f1l, f2l = f1[loc], f2[loc]
                V = self.sample_vmf(xp.broadcast_to(f2l, (Mc,) + f2l.shape).copy())     # (Mc, n, 4)
                lr = xp.sum(V * (f1l - f2l)[None], axis=-1) - cc[loc][None]          # log p1/p2 at V
                ar = xp.maximum(1.0 - xp.exp(lr), 0.0)
                ok = self.uniform(ar.shape) * amax[loc][None] <= ar
                anyok = ok.any(axis=0)
                first = xp.argmax(ok, axis=0)
                pick = V[first, xp.arange(V.shape[1])]
                out[loc[anyok]] = pick[anyok]
                loc = loc[~anyok]
                if loc.size == 0:
                    break
            else:
                raise RuntimeError("residual sampler did not converge")
            flatq2[pend] = out
        return q1, q2


# ====================================================================================================================== geometry

class Geometry:
    """Index tables for a box of side ell (fine sites) in a non-periodic frame of side ell + 8 (box at offset 4, so the box
    origin is a coarse site). Links are indexed lid = site_index * 4 + mu; index NL is an extra identity link (padding)."""

    def __init__(self, ell, w=W_STAPLE):
        assert ell % 2 == 0
        self.ell, self.w = ell, w
        self.F = F = ell + 8
        self.off = off = 4
        self.NL = NL = F ** 4 * 4
        E = np.eye(4, dtype=int)

        def inside(x):
            return all(0 <= c < F for c in x)

        def lid(x, mu):
            return (((x[0] * F + x[1]) * F + x[2]) * F + x[3]) * 4 + mu

        self.lid = lid

        def inbox(x):
            return all(off <= c < off + ell for c in x)

        sites = [tuple(x) for x in np.ndindex(F, F, F, F)]
        dyn = [(x, mu) for x in sites if inbox(x) for mu in range(4)]
        self.dyn_lids = np.array([lid(x, mu) for x, mu in dyn])
        dynset = set(self.dyn_lids.tolist())
        self.dynset = dynset

        # blurred paths of coarse links: list of (coef, [(lid, dag)])
        def paths(y, mu):
            out = [(1.0, [((y), mu, 0), (tuple(np.add(y, E[mu])), mu, 0)])]
            for nu in range(4):
                if nu == mu:
                    continue
                for s in (1, -1):
                    if s == 1:
                        el = [(y, nu, 0), (tuple(np.add(y, E[nu])), mu, 0), (tuple(np.add(y, E[nu] + E[mu])), mu, 0),
                              (tuple(np.add(y, 2 * E[mu])), nu, 1)]
                    else:
                        el = [(tuple(np.add(y, -E[nu])), nu, 1), (tuple(np.add(y, -E[nu])), mu, 0),
                              (tuple(np.add(y, -E[nu] + E[mu])), mu, 0), (tuple(np.add(y, -E[nu] + 2 * E[mu])), nu, 0)]
                    out.append((w, el))
            return out

        def ok_path(el):
            for (x, nu, _) in el:
                if not inside(x) or not inside(tuple(np.add(x, E[nu]))):
                    return False
            return True

        CL = []
        for y in sites:
            if any(c % 2 for c in y):
                continue
            for mu in range(4):
                ps = paths(y, mu)
                if not all(ok_path(el) for _, el in ps):
                    continue
                if any(lid(x, nu) in dynset for _, el in ps for (x, nu, _) in el):
                    CL.append((y, mu, [(c, [(lid(x, nu), d) for (x, nu, d) in el]) for c, el in ps]))
        self.ncl = ncl = len(CL)
        self.cl_paths = np.full((ncl + 1, 7, 4), NL, dtype=np.int64)
        self.cl_dag = np.zeros((ncl + 1, 7, 4), dtype=np.int64)
        self.cl_coef = np.zeros((ncl + 1, 7))
        entries = {}
        for i, (y, mu, ps) in enumerate(CL):
            for p, (c, el) in enumerate(ps):
                self.cl_coef[i, p] = c
                for k, (l, d) in enumerate(el):
                    self.cl_paths[i, p, k] = l
                    self.cl_dag[i, p, k] = d
                    if l in dynset:
                        entries.setdefault(l, []).append((i, c, el[:k], el[k + 1:], d))
        self.cl_site = [(y, mu) for (y, mu, _) in CL]

        # shell: non-dynamic links in Wilson staples of dynamic links or in blurred paths of constraint coarse links
        shell = set()

        def staples(x, mu):
            st = []
            for nu in range(4):
                if nu == mu:
                    continue
                st.append([(tuple(np.add(x, E[mu])), nu, 0), (tuple(np.add(x, E[nu])), mu, 1), (x, nu, 1)])
                st.append([(tuple(np.add(x, E[mu] - E[nu])), nu, 1), (tuple(np.add(x, -E[nu])), mu, 1),
                           (tuple(np.add(x, -E[nu])), nu, 0)])
            return st

        # colour classes
        classes = {}
        for x, mu in dyn:
            key = (mu,) + tuple(c % 3 for c in x)
            classes.setdefault(key, []).append((x, mu))
        self.Emax = Emax = max(len(v) for v in entries.values())
        self.classes = []
        for key in sorted(classes):
            members = classes[key]
            n = len(members)
            c_lid = np.array([lid(x, mu) for x, mu in members])
            stp = np.zeros((n, 6, 3), dtype=np.int64)
            stpd = np.zeros((n, 6, 3), dtype=np.int64)
            e_l = np.full((n, Emax), ncl, dtype=np.int64)
            e_c = np.zeros((n, Emax))
            e_pre = np.full((n, Emax, 3), NL, dtype=np.int64)
            e_pred = np.zeros((n, Emax, 3), dtype=np.int64)
            e_suf = np.full((n, Emax, 3), NL, dtype=np.int64)
            e_sufd = np.zeros((n, Emax, 3), dtype=np.int64)
            e_dag = np.zeros((n, Emax), dtype=np.int64)
            e_mask = np.zeros((n, Emax))
            for i, (x, mu) in enumerate(members):
                for s, st in enumerate(staples(x, mu)):
                    for k, (y, nu, d) in enumerate(st):
                        stp[i, s, k] = lid(y, nu)
                        stpd[i, s, k] = d
                        if lid(y, nu) not in dynset:
                            shell.add(lid(y, nu))
                for j, (l, c, pre, suf, d) in enumerate(entries.get(lid(x, mu), [])):
                    e_l[i, j], e_c[i, j], e_dag[i, j], e_mask[i, j] = l, c, d, 1.0
                    for k, (ll, dd) in enumerate(pre):
                        e_pre[i, j, k], e_pred[i, j, k] = ll, dd
                    for k, (ll, dd) in enumerate(suf):
                        e_suf[i, j, k], e_sufd[i, j, k] = ll, dd
            self.classes.append(dict(lid=c_lid, stp=stp, stpd=stpd, e_l=e_l, e_c=e_c, e_pre=e_pre, e_pred=e_pred,
                                     e_suf=e_suf, e_sufd=e_sufd, e_dag=e_dag, e_mask=e_mask))
        for i in range(ncl):
            for p in range(7):
                for k in range(4):
                    l = self.cl_paths[i, p, k]
                    if l != NL and l not in dynset:
                        shell.add(int(l))
        self.shell = np.array(sorted(shell))

        # free sites for the gauge alignment, by parity
        free = {0: [], 1: []}
        for x in sites:
            if not inbox(x) or all(c % 2 == 0 for c in x):
                continue
            if all(x[m] >= off + 1 for m in range(4)):
                outl = [lid(x, m) for m in range(4)]
                inl = [lid(tuple(np.subtract(x, E[m])), m) for m in range(4)]
                free[sum(x) % 2].append((outl, inl))
        self.free = {p: (np.array([o for o, _ in v]), np.array([i for _, i in v])) for p, v in free.items()}

        # box plaquettes (all six planes, base site in the box, all four links inside the frame) for observables
        plaq = []
        for x in sites:
            if not inbox(x):
                continue
            for m in range(4):
                for n in range(m + 1, 4):
                    plaq.append([(lid(x, m), 0), (lid(tuple(np.add(x, E[m])), n), 0),
                                 (lid(tuple(np.add(x, E[n])), m), 1), (lid(x, n), 1)])
        self.plaq = np.array([[l for l, _ in p] for p in plaq])
        self.plaqd = np.array([[d for _, d in p] for p in plaq])

    def to_device(self, xp):
        for c in self.classes:
            for k in list(c):
                c[k] = xp.asarray(c[k])
        self.cl_paths_d = xp.asarray(self.cl_paths)
        self.cl_dag_d = xp.asarray(self.cl_dag)
        self.cl_coef_d = xp.asarray(self.cl_coef)
        self.dyn_d = xp.asarray(self.dyn_lids)
        self.free_d = {p: (xp.asarray(o), xp.asarray(i)) for p, (o, i) in self.free.items()}
        self.plaq_d, self.plaqd_d = xp.asarray(self.plaq), xp.asarray(self.plaqd)


# ====================================================================================================================== sampler

class PairSampler:
    """P coupled pairs: U of shape (P, 2, NL + 1, 4), Y of shape (P, 2, ncl + 1, 4)."""

    def __init__(self, be, geo, beta, kappa, U, Y):
        self.be, self.geo, self.beta, self.kappa = be, geo, beta, kappa
        self.U, self.Y = U, Y

    def gather(self, idx, dag):
        """Quaternions U[:, :, idx], conjugated where dag."""
        be = self.be
        g = self.U[:, :, idx]
        return be.xp.where(dag[..., None].astype(bool), g * be.conj, g)

    def prod(self, idx, dag):
        """Ordered product over the last index axis of idx."""
        be = self.be
        out = self.gather(idx[..., 0], dag[..., 0])
        for k in range(1, idx.shape[-1]):
            out = be.qmul(out, self.gather(idx[..., k], dag[..., k]))
        return out

    def phi(self, l):
        """Phi for coarse-link indices l (any shape), per chain: (P, 2, *l.shape, 4)."""
        g = self.geo
        pr = self.prod(g.cl_paths_d[l], g.cl_dag_d[l])                 # (P, 2, *l.shape, 7, 4)
        return self.be.xp.sum(pr * g.cl_coef_d[l][..., None], axis=-2)

    def update_class(self, c):
        """One colour class. Proposal: heat bath from exp(q . F(U)), F(U) = beta conj(W) + kappa sum_entries c
        <Y_l - lambda_l Phi_hat_l, Pre q Suf>-field, i.e. the constraint exponent with the normaliser -log z(kappa |Phi_l|)
        linearised at the current state (lambda_l = (log z)'(kappa |Phi_l(U)|)). The proposal depends on the current link
        through Phi_l(U), so the acceptance is the full Metropolis-Hastings ratio (exact for any lambda)."""
        be, xp = self.be, self.be.xp
        k = self.kappa
        W = xp.sum(self.prod(c["stp"], c["stpd"]), axis=-2)            # (P, 2, n, 4)
        Fw = self.beta * W * be.conj
        qo = self.U[:, :, c["lid"]]
        if k == 0.0:
            q1, q2 = be.coupled_vmf(Fw[:, 0], Fw[:, 1])
            qn = xp.stack([q1, q2], axis=1)
            self.U[:, :, c["lid"]] = qn / xp.linalg.norm(qn, axis=-1, keepdims=True)
            return
        # entry path = Pre U^(dag) Suf; <Z, Pre U Suf> = U . conj(Suf Z^dag Pre); with U^dag: U . (Suf Z^dag Pre)
        Pre = self.prod(c["e_pre"], c["e_pred"])                        # (P, 2, n, E, 4)
        Suf = self.prod(c["e_suf"], c["e_sufd"])
        Yl = self.Y[:, :, c["e_l"]]
        dag = c["e_dag"][..., None].astype(bool)
        wgt = (k * c["e_c"] * c["e_mask"])[..., None]

        def field(Z):
            M = be.qmul(be.qmul(Suf, Z * be.conj), Pre)
            return xp.sum(xp.where(dag, M, M * be.conj) * wgt, axis=-2)

        def prop_field(Phi):
            r = xp.linalg.norm(Phi, axis=-1)
            lam = self.be.dlog_z(k * r)
            hat = Phi / xp.maximum(r, 1e-12)[..., None]
            return Fw + field(Yl - lam[..., None] * hat)

        F_lin = Fw + field(Yl)                                          # exact linear part of the log target
        Phi_o = self.phi(c["e_l"])                                      # (P, 2, n, E, 4)
        F_o = prop_field(Phi_o)
        q1, q2 = be.coupled_vmf(F_o[:, 0], F_o[:, 1])
        qn = xp.stack([q1, q2], axis=1)                                 # (P, 2, n, 4)
        dn = xp.where(dag, qn[:, :, :, None] * be.conj, qn[:, :, :, None])
        do = xp.where(dag, qo[:, :, :, None] * be.conj, qo[:, :, :, None])
        Phi_n = Phi_o + be.qmul(be.qmul(Pre, dn - do), Suf) * c["e_c"][..., None]
        F_n = prop_field(Phi_n)
        lz_o = xp.sum(c["e_mask"] * be.log_z(k * xp.linalg.norm(Phi_o, axis=-1)), axis=-1)
        lz_n = xp.sum(c["e_mask"] * be.log_z(k * xp.linalg.norm(Phi_n, axis=-1)), axis=-1)
        log_target = xp.sum((qn - qo) * F_lin, axis=-1) - (lz_n - lz_o)
        log_q_fwd = xp.sum(qn * F_o, axis=-1) - be.log_z(xp.linalg.norm(F_o, axis=-1))
        log_q_rev = xp.sum(qo * F_n, axis=-1) - be.log_z(xp.linalg.norm(F_n, axis=-1))
        u = be.uniform((qn.shape[0], 1, qn.shape[2]))                   # shared by the two chains of a pair
        acc = xp.log(xp.maximum(u, 1e-300)) <= (log_target + log_q_rev - log_q_fwd)
        self.acc_sum = getattr(self, "acc_sum", 0.0) + float(xp.mean(acc))
        self.acc_n = getattr(self, "acc_n", 0) + 1
        qn = xp.where(acc[..., None], qn, qo)
        self.U[:, :, c["lid"]] = qn / xp.linalg.norm(qn, axis=-1, keepdims=True)

    def sweep(self):
        for c in self.geo.classes:
            self.update_class(c)

    def align(self, passes=2):
        """Gauge-align chain B to chain A at free sites (exact symmetry of B's law)."""
        be, xp = self.be, self.be.xp
        for _ in range(passes):
            for p in (0, 1):
                o, i = self.geo.free_d[p]
                if o.size == 0:
                    continue
                Ao, Bo = self.U[:, 0, o], self.U[:, 1, o]               # (P, ns, 4, 4)
                Ai, Bi = self.U[:, 0, i], self.U[:, 1, i]
                K = xp.sum(be.qmul(Bo, Ao * be.conj), axis=-2) + xp.sum(be.qmul(Bi * be.conj, Ai), axis=-2)
                g = K * be.conj
                g = g / xp.maximum(xp.linalg.norm(g, axis=-1, keepdims=True), 1e-300)
                self.U[:, 1, o] = be.qmul(g[:, :, None], Bo)
                self.U[:, 1, i] = be.qmul(Bi, (g * be.conj)[:, :, None])

    def disagreement(self):
        be, xp = self.be, self.be.xp
        A = self.U[:, 0, self.geo.dyn_d]
        B = self.U[:, 1, self.geo.dyn_d]
        dot = xp.clip(xp.abs(xp.sum(A * B, axis=-1)), 0.0, 1.0)
        dist = 2.0 * xp.arccos(dot)                                     # SO(3)-type angle, centre-blind
        dif = xp.linalg.norm(A - B, axis=-1)
        return xp.sum(dif > TOL, axis=-1), xp.sum(dist, axis=-1)

    def plaquettes(self):
        """(P, 2, nplaq) fundamental (1/2 tr) of the box plaquettes."""
        return self.prod(self.geo.plaq_d, self.geo.plaqd_d)[..., 0]


# ====================================================================================================================== set-up

def frame_links(Ufull, geo, shift):
    """Links of the frame from a periodic configuration Ufull (4, N, N, N, N, 4) (direction first), shifted by shift."""
    N = Ufull.shape[1]
    F = geo.F
    idx = [(np.arange(F) + shift[d]) % N for d in range(4)]
    sub = Ufull[:, idx[0]][:, :, idx[1]][:, :, :, idx[2]][:, :, :, :, idx[3]]     # (4, F, F, F, F, 4)
    links = np.transpose(sub, (1, 2, 3, 4, 0, 5)).reshape(F ** 4 * 4, 4)
    return np.concatenate([links, np.array([[1.0, 0.0, 0.0, 0.0]])], axis=0)


def sample_Y(be, geo, kappa, Uframe):
    """Y_l ~ exp(kappa <Y, Phi_l(U)>) given frame links Uframe (B, NL+1, 4) (numpy or xp)."""
    xp = be.xp
    tmp = PairSampler(be, geo, 0.0, kappa, xp.asarray(Uframe)[:, None], None)
    ph = tmp.phi(xp.arange(geo.ncl))[:, 0]                              # (B, ncl, 4)
    Y = be.sample_vmf(kappa * ph)
    one = xp.zeros(Y.shape[:-2] + (1, 4))
    one[..., 0] = 1.0
    return xp.concatenate([Y, one], axis=-2)


def rot(theta):
    return np.array([math.cos(theta / 2), 0.0, 0.0, math.sin(theta / 2)])


def twist_Y(be, geo, Y):
    """A3: flip Y on coarse links (y, mu=1) with y_0 at the box centre slice and y_2 >= box centre: block plaquettes in the
    (0, 1) planes along that half-slice change sign (a centre twist sheet ending inside the box)."""
    c = geo.off + geo.ell // 2
    c -= c % 2
    sel = [i for i, (y, mu) in enumerate(geo.cl_site) if mu == 1 and y[0] == c and y[2] >= c]
    Y = Y.copy()
    Y[..., sel, :] *= -1.0
    return Y


def a4_Y(geo, Y):
    """A4: one block link on the box boundary rotated by angle pi (Y -> i sigma_3 Y): the block plaquettes through it jump."""
    lo = geo.off
    cand = [i for i, (y, mu) in enumerate(geo.cl_site) if y[0] == lo and mu == 1 and all(lo <= c < lo + geo.ell for c in y[1:])]
    i = cand[len(cand) // 2]
    Y = Y.copy()
    Y[..., i, :] = be_qmul_np(np.array([0.0, 0.0, 0.0, 1.0]), Y[..., i, :])
    return Y, i


def a6_outside(geo, U):
    """A6: a thin centre-vortex sheet in the outside that ends on the box: the frozen links (x, mu=1) with x_0 = box centre
    slice, x_2 >= box centre, x outside the box, flipped (-1). The boundary of that half-slice is a (0,1)-plaquette sheet
    which ends on the box (the UV-TV.md section 3 example)."""
    c = geo.off + geo.ell // 2
    F, lo, hi = geo.F, geo.off, geo.off + geo.ell
    sel = []
    for x in np.ndindex(F, F, F, F):
        if x[0] == c and x[2] >= c and not all(lo <= v < hi for v in x) and x[1] + 1 < F:
            sel.append(geo.lid(x, 1))
    U = U.copy()
    U[..., sel, :] *= -1.0
    return U


def gauge_transform(geo, U, Y, g):
    """Gauge transformation g (one quaternion per frame site, shape (F^4, 4)) of frame links U (..., NL+1, 4) and of the
    block variables Y (..., ncl+1, 4) at their coarse end points: U(x,mu) -> g(x) U g(x+mu)^dag."""
    F = geo.F
    E = np.eye(4, dtype=int)
    U = U.copy()
    Y = Y.copy()
    idx = np.arange(F ** 4)
    coords = np.stack(np.unravel_index(idx, (F,) * 4), axis=-1)
    for mu in range(4):
        tgt = coords + E[mu]
        ok = (tgt < F).all(axis=-1)
        src = idx[ok]
        t = np.ravel_multi_index(tuple(tgt[ok].T), (F,) * 4)
        lids = src * 4 + mu
        U[..., lids, :] = be_qmul_np(be_qmul_np(g[src], U[..., lids, :]), g[t] * CONJ)
    for i, (y, mu) in enumerate(geo.cl_site):
        a = np.ravel_multi_index(tuple(y), (F,) * 4)
        b = np.ravel_multi_index(tuple(np.add(y, 2 * E[mu])), (F,) * 4)
        Y[..., i, :] = be_qmul_np(be_qmul_np(g[a], Y[..., i, :]), g[b] * CONJ)
    return U, Y


def gpu_idle(threshold=15, samples=3):
    """True if the GPU utilisation stays below `threshold` % over `samples` readings one second apart."""
    import subprocess
    vals = []
    for _ in range(samples):
        out = subprocess.run(["nvidia-smi", "--query-gpu=utilization.gpu", "--format=csv,noheader,nounits"],
                             capture_output=True, text=True).stdout.strip().splitlines()
        vals.append(max(int(v) for v in out) if out else 100)
        time.sleep(1)
    return max(vals) < threshold, vals


# ====================================================================================================================== commands

def load_confs(path):
    d = np.load(path)
    return d["U"], float(d["beta"])            # (n, 4, N, N, N, N, 4)


def build_pairs(be, geo, confs, kappa, specs, yclass, rng):
    """specs: list of (start_conf, outside_conf, shift, kind, which, theta) per pair; kind "z" rotates the outside link `which`
    of chain B by the angle theta, kind "y" the block variable `which`, kind "none" nothing. One instance = one
    (outside_conf, shift): its block field Y is sampled once given the outside configuration (the equilibrium U0) and shared
    by every pair of the instance. Returns U (P, 2, NL+1, 4), Y (P, 2, ncl+1, 4)."""
    xp = be.xp
    P = len(specs)
    U = xp.empty((P, 2, geo.NL + 1, 4)) if be.gpu else np.zeros((P, 2, geo.NL + 1, 4))
    cache = {}
    for p, (s_idx, o_idx, shift, kind, which, theta) in enumerate(specs):
        key = (s_idx, o_idx, shift)
        if key not in cache:
            out = frame_links(confs[o_idx], geo, shift)
            start = frame_links(confs[s_idx], geo, shift)
            base = out.copy()
            base[geo.dyn_lids] = start[geo.dyn_lids]
            if yclass == "A6":
                base = a6_outside(geo, base)
            cache[key] = base
        base = cache[key]
        b1 = base
        if kind == "z":
            b1 = base.copy()
            b1[which] = be_qmul_np(rot(theta), base[which])
        U[p, 0] = xp.asarray(base) if be.gpu else base
        U[p, 1] = xp.asarray(b1) if be.gpu else b1
    keys = sorted({(o, sh) for (_, o, sh, _, _, _) in specs})
    Ufr = np.stack([frame_links(confs[o], geo, sh) for (o, sh) in keys])
    Yk = sample_Y(be, geo, kappa, Ufr)                                  # (K, ncl+1, 4)
    Yk = be.xp.asnumpy(Yk) if be.gpu else Yk
    if yclass == "A3":
        Yk = twist_Y(be, geo, Yk)
    elif yclass == "A1":
        Yk[..., :, :] = np.array([1.0, 0.0, 0.0, 0.0])
    elif yclass == "A2":
        r = rng.standard_normal(Yk.shape)
        Yk = r / np.linalg.norm(r, axis=-1, keepdims=True)
        Yk[..., -1, :] = np.array([1.0, 0.0, 0.0, 0.0])
    elif yclass == "A4":
        Yk, _ = a4_Y(geo, Yk)
    elif yclass == "A5":
        raise NotImplementedError("A5 needs pure SO(3) (adjoint) Wilson configurations; no adjoint generator exists yet")
    kidx = {k: i for i, k in enumerate(keys)}
    Y = np.stack([Yk[kidx[(o, sh)]] for (_, o, sh, _, _, _) in specs])
    Y2 = np.stack([Y, Y.copy()], axis=1)
    for p, (_, _, _, kind, which, theta) in enumerate(specs):
        if kind == "y":
            Y2[p, 1, which] = be_qmul_np(rot(theta), Y2[p, 1, which])
    return (U if be.gpu else xp.asarray(U)), xp.asarray(Y2)


def be_qmul_np(a, b):
    a0, a1, a2, a3 = a[..., 0], a[..., 1], a[..., 2], a[..., 3]
    b0, b1, b2, b3 = b[..., 0], b[..., 1], b[..., 2], b[..., 3]
    return np.stack([a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3, a0 * b1 + b0 * a1 - (a2 * b3 - a3 * b2),
                     a0 * b2 + b0 * a2 - (a3 * b1 - a1 * b3), a0 * b3 + b0 * a3 - (a1 * b2 - a2 * b1)], axis=-1)


def heat_start(be, geo, beta, U, Y, idx, sweeps=20, sampler=None):
    """Start 1 (amendment A3): the equilibrium interior U0, heated by `sweeps` heat-bath sweeps at kappa = 0 (unconstrained,
    unperturbed boundary of chain A), copied into both chains of each pair in idx. A different equilibrium configuration's
    interior is not usable as a second start: the constraint pins the coarse-site gauge and local updates relax it only
    over very many sweeps (pilot of 2026-11-23)."""
    xp = be.xp
    if len(idx) == 0:
        return U
    idx = xp.asarray(idx)
    sub = U[idx][:, [0, 0]].copy()
    H = (sampler or PairSampler)(be, geo, beta, 0.0, sub, Y[idx][:, [0, 0]].copy())
    for _ in range(sweeps):
        H.sweep()
    dyn = geo.dyn_d
    for ch in (0, 1):
        blk = U[idx, ch]
        blk[:, dyn] = H.U[:, 0][:, dyn]
        U[idx, ch] = blk
    return U


def sync(be):
    if be.gpu:
        be.xp.cuda.Stream.null.synchronize()


def run_chains(be, geo, beta, kappa, U, Y, sweeps, every, align=True, deadline=None, sampler=None, snap=None):
    """Run, measuring every `every` sweeps: disagreement count and W1-type sum per pair, box plaquettes per chain.
    Stops early (after a measurement) once time.time() passes `deadline`; the number of sweeps done is returned."""
    xp = be.xp
    S = (sampler or PairSampler)(be, geo, beta, kappa, U, Y)
    rec_d, rec_w, plaq_sum, nmeas = [], [], None, 0
    done = 0
    for t in range(1, sweeps + 1):
        S.sweep()
        done = t
        if snap and t in snap:
            snap[t](S)
        if t % every == 0:
            if align:
                S.align()
            d, w = S.disagreement()
            rec_d.append(d)
            rec_w.append(w)
            pl = S.plaquettes()
            plaq_sum = pl if plaq_sum is None else plaq_sum + pl
            nmeas += 1
            if deadline is not None and time.time() > deadline:
                break
    tohost = (lambda a: xp.asnumpy(a)) if be.gpu else (lambda a: np.asarray(a))
    return dict(d=tohost(xp.stack(rec_d)), w=tohost(xp.stack(rec_w)), plaq=tohost(plaq_sum / max(nmeas, 1)), S=S,
                sweeps_done=done)


def plaq01(U):
    """Mean (1/2) tr of the (0, 1) plaquettes of periodic configurations U (B, 4, N, N, N, N, 4)."""
    A, B = U[:, 0], U[:, 1]
    Bx = np.roll(B, -1, axis=1)
    Ay = np.roll(A, -1, axis=2)
    p = be_qmul_np(be_qmul_np(be_qmul_np(A, Bx), Ay * CONJ), B * CONJ)
    return float(p[..., 0].mean())


def cmd_gen(a):
    """Equilibrium 16^4 SU(2) configurations on the GPU (gpu/gauge.py, unchanged), saved as quaternions."""
    import cupy as cp
    sys.path.insert(0, LAT)
    sys.path.insert(0, os.path.join(LAT, "gpu"))
    import gauge as G
    import boundary as bd
    t0 = time.time()
    g = G.Gauge(16, 16, a.beta, nc=2, B=a.nconf, seed=a.seed, start="hot")
    for _ in range(a.therm):
        g.sweep(3)
    cp.cuda.Stream.null.synchronize()
    t1 = time.time()
    U = np.stack([cp.asnumpy(bd.m2q(g.U[mu], cp)) for mu in range(4)], axis=1)   # (B, 4, 16, 16, 16, 16, 4)
    pl = plaq01(U)
    np.savez(a.out, U=U, beta=a.beta, therm=a.therm, seconds=t1 - t0, plaq=pl)
    print(json.dumps(dict(out=a.out, nconf=a.nconf, therm=a.therm, seconds=round(t1 - t0, 2), plaq01=round(pl, 5),
                          sec_per_conf_sweep=(t1 - t0) / (a.therm * a.nconf))))


THETAS = (math.pi / 2, math.pi)


def shell_and_y_specs(geo, rng, n_shell, n_y, s_starts, o_idx, shift, thetas=THETAS):
    """One instance: n_shell outside links and n_y block variables, each rotated by every theta, for every start."""
    z = rng.choice(geo.shell, size=n_shell, replace=False)
    yl = rng.choice(geo.ncl, size=n_y, replace=False) if n_y else []
    specs = []
    for s_idx in s_starts:
        for th in thetas:
            specs += [(s_idx, o_idx, shift, "z", int(zz), th) for zz in z]
            specs += [(s_idx, o_idx, shift, "y", int(l), th) for l in yl]
    return specs


def cmd_pilot(a):
    be = Backend(a.gpu, a.seed)
    confs, beta_c = load_confs(a.conf)
    geo = Geometry(a.ell)
    geo.to_device(be.xp)
    rng = np.random.default_rng(a.seed)
    shift = (0, 0, 0, 0)
    specs = shell_and_y_specs(geo, rng, a.pairs, 0, [0, 0], 0, shift, thetas=(math.pi / 2,))
    U, Y = build_pairs(be, geo, confs, a.kappa, specs, "sampled", rng)
    U = heat_start(be, geo, a.beta, U, Y, list(range(len(specs) // 2, len(specs))))
    sync(be)
    t0 = time.time()
    r = run_chains(be, geo, a.beta, a.kappa, U, Y, a.sweeps, a.every)
    sync(be)
    dt = time.time() - t0
    P = len(specs)
    half = P // 2
    d = r["d"].astype(float)
    out = dict(beta=a.beta, ell=a.ell, kappa=a.kappa, sweeps=a.sweeps, every=a.every, pairs=P, seconds=dt,
               sec_per_sweep=dt / a.sweeps, n_box_links=int(len(geo.dyn_lids)), ncl=int(geo.ncl),
               n_shell=int(len(geo.shell)), n_classes=len(geo.classes),
               d_start0=d[:, :half].mean(axis=1).tolist(), d_start1=d[:, half:].mean(axis=1).tolist(),
               w_start0=r["w"][:, :half].mean(axis=1).tolist(), w_start1=r["w"][:, half:].mean(axis=1).tolist(),
               plaq_mean=float(r["plaq"].mean()), plaq_start0=float(r["plaq"][:half].mean()),
               plaq_start1=float(r["plaq"][half:].mean()),
               mh_acceptance=getattr(r["S"], "acc_sum", 0.0) / max(getattr(r["S"], "acc_n", 0), 1))
    json.dump(out, open(a.out, "w"), indent=1)
    print(json.dumps({k: out[k] for k in ("beta", "ell", "kappa", "sweeps", "pairs", "seconds", "sec_per_sweep",
                                          "plaq_start0", "plaq_start1", "mh_acceptance")}))


def cmd_job(a):
    """`batch` W2 jobs in one launch (W2-PREREG.md section 8). Per job: a greedy pool of `pool` outsides (8 shell links,
    theta = pi/2, one start, T/10 sweeps), then the worst outside with 32 shell links + 8 block variables, each at both
    angles, x 2 starts (160 pairs), for T sweeps. Wall times recorded."""
    if a.gpu and not a.force:
        idle, vals = gpu_idle()
        if not idle:
            sys.exit(f"GPU not idle (utilisation {vals} %); refusing to start (use --force to override)")
    t_start = time.time()
    deadline = t_start + a.max_seconds if a.max_seconds else None
    be = Backend(a.gpu, a.seed)
    confs, _ = load_confs(a.conf)
    t_setup0 = time.time()
    geo = Geometry(a.ell)
    geo.to_device(be.xp)
    t_geo = time.time() - t_setup0
    rng = np.random.default_rng(a.seed)
    nconf = confs.shape[0]
    pools = [[(int(rng.integers(nconf)), tuple(int(v) for v in rng.integers(0, 16, 4))) for _ in range(max(a.pool, 1))]
             for _ in range(a.batch)]
    sync(be)
    t0 = time.time()
    Tp = max(a.every, a.T // 10)
    if a.pool > 0:
        pool_specs = []
        for pool in pools:
            zsel = rng.choice(geo.shell, size=8, replace=False)
            for (ci, sh) in pool:
                pool_specs += [(ci, ci, sh, "z", int(z), math.pi / 2) for z in zsel]
        U, Y = build_pairs(be, geo, confs, a.kappa, pool_specs, a.yclass, rng)
        rp = run_chains(be, geo, a.beta, a.kappa, U, Y, Tp, a.every)
        pl = rp["plaq"]                                                 # (P, 2, nplaq)
        klow = np.abs(pl[:, 0] - pl[:, 1]).max(axis=-1).reshape(a.batch, a.pool, 8).sum(axis=2)
        worst = [int(w) for w in np.argmax(klow, axis=1)]
        del U, Y, rp
    else:                                                               # equilibrium outside, no greedy pool
        pool_specs, worst = [], [0] * a.batch
    sync(be)
    t_pool = time.time() - t0
    t1 = time.time()
    specs, heat = [], []
    for b in range(a.batch):
        ci, sh = pools[b][worst[b]]
        sp = shell_and_y_specs(geo, rng, 32, 8, [ci, ci], ci, sh)
        heat += list(range(len(specs) + len(sp) // 2, len(specs) + len(sp)))
        specs += sp
    U, Y = build_pairs(be, geo, confs, a.kappa, specs, a.yclass, rng)
    U = heat_start(be, geo, a.beta, U, Y, heat)
    sync(be)
    t_build = time.time() - t1
    t2 = time.time()
    r = run_chains(be, geo, a.beta, a.kappa, U, Y, a.T, a.every, deadline=deadline)
    sync(be)
    t_main = time.time() - t2
    done = r["sweeps_done"]
    d = r["d"].astype(float).reshape(r["d"].shape[0], a.batch, 2, -1)  # (meas, job, start, pairs)
    out = dict(beta=a.beta, ell=a.ell, kappa=a.kappa, yclass=a.yclass, T=a.T, every=a.every, pool=a.pool, pool_T=Tp,
               batch=a.batch, pairs=len(specs), pool_pairs=len(pool_specs), gpu=a.gpu, seconds_geometry=t_geo,
               seconds_pool=t_pool, seconds_build=t_build, seconds_main=t_main,
               seconds_total=t_geo + t_pool + t_build + t_main, sec_per_sweep_main=t_main / done, sweeps_done=done,
               capped=done < a.T, max_seconds=a.max_seconds,
               seconds_full_T_extrapolated=t_geo + t_pool + t_build + t_main / done * a.T,
               sec_per_sweep_pool=(t_pool / Tp if a.pool > 0 else 0.0), seconds_per_job=(t_geo + t_pool + t_build + t_main) / a.batch,
               n_box_links=int(len(geo.dyn_lids)), ncl=int(geo.ncl), n_shell=int(len(geo.shell)),
               d_start0=d[:, :, 0].mean(axis=(1, 2)).tolist(), d_start1=d[:, :, 1].mean(axis=(1, 2)).tolist(),
               plaq_mean=float(r["plaq"].mean()), worst_pool=worst)
    if a.gpu:
        import cupy as cp
        out["gpu_mem_bytes"] = int(cp.get_default_memory_pool().total_bytes())
    json.dump(out, open(a.out, "w"), indent=1)
    print(json.dumps({k: out[k] for k in ("beta", "ell", "kappa", "yclass", "T", "sweeps_done", "capped", "batch", "pairs",
                                          "seconds_pool", "seconds_main", "seconds_total", "seconds_full_T_extrapolated",
                                          "sec_per_sweep_main", "plaq_mean")}))


def cmd_launch(a):
    """One production launch of the narrow run (amendment A6): a mixed list of jobs, e.g. "A3:8,A1:8,A2:0,A4:0,A6:0,sampled:0"
    (instance class : pool size). Pool jobs get a greedy pool phase (pool x 8 shell links, theta = pi, T/10 sweeps), all pool
    jobs of the launch together; then every job runs 32 shell links + 8 block variables at theta = pi, x 2 starts (80 pairs),
    all jobs in one launch, for T sweeps (fused update with --fused). Saves one compressed npz with the per-pair results and
    the lever data (see PIPELINE.md, "Saved for the two-level classification")."""
    import cupy as cp
    if a.gpu and not a.force:
        idle, vals = gpu_idle()
        if not idle:
            sys.exit(f"GPU not idle (utilisation {vals} %); refusing to start (use --force to override)")
    t_start = time.time()
    deadline = t_start + a.max_seconds if a.max_seconds else None
    smp = None
    if a.fused:
        import fused as Fz
        smp = Fz.FusedSampler
    jobs = []
    for tok in a.jobs.split(","):
        y, pz = tok.split(":")
        jobs.append((y, int(pz)))
    be = Backend(a.gpu, a.seed)
    xp = be.xp
    confs, _ = load_confs(a.conf)
    nconf = confs.shape[0]
    geo = Geometry(a.ell)
    geo.to_device(xp)
    rng = np.random.default_rng(a.seed)
    th = (math.pi,)
    t_geo = time.time() - t_start
    # ---------------------------------------------------------------- pool phase (pool jobs together)
    t0 = time.time()
    Tp = max(a.every, a.T // 10)
    inst = []
    pool_jobs = [j for j, (_, pz) in enumerate(jobs) if pz > 0]
    pools = {}
    for j, (y, pz) in enumerate(jobs):
        cand = [(int(rng.integers(nconf)), tuple(int(v) for v in rng.integers(0, 16, 4))) for _ in range(max(pz, 1))]
        pools[j] = cand
    klow_pool = {}
    if pool_jobs:
        P_pool = sum(jobs[j][1] * 8 for j in pool_jobs)
        Upool = xp.empty((P_pool, 2, geo.NL + 1, 4))
        Ypool = xp.empty((P_pool, 2, geo.ncl + 1, 4))
        k = 0
        for j in pool_jobs:
            y, pz = jobs[j]
            sp = []
            zsel = rng.choice(geo.shell, size=8, replace=False)
            for (ci, sh) in pools[j]:
                sp += [(ci, ci, sh, "z", int(z), math.pi) for z in zsel]
            Uj, Yj = build_pairs(be, geo, confs, a.kappa, sp, y, rng)
            Upool[k:k + len(sp)] = Uj
            Ypool[k:k + len(sp)] = Yj
            k += len(sp)
            del Uj, Yj
        rp = run_chains(be, geo, a.beta, a.kappa, Upool, Ypool, Tp, a.every, sampler=smp)
        pl = rp["plaq"]
        k = 0
        for j in pool_jobs:
            pz = jobs[j][1]
            blk = pl[k:k + pz * 8]
            kl = np.abs(blk[:, 0] - blk[:, 1]).max(axis=-1).reshape(pz, 8).sum(axis=1)
            klow_pool[j] = kl.tolist()
            inst.append((j, pools[j][int(np.argmax(kl))]))
            k += pz * 8
        del Upool, Ypool, rp
    for j, (y, pz) in enumerate(jobs):
        if pz == 0:
            inst.append((j, pools[j][0]))
    inst.sort()
    sync(be)
    t_pool = time.time() - t0
    # ---------------------------------------------------------------- main
    t1 = time.time()
    per_job = 2 * 40
    P = per_job * len(jobs)
    U = xp.empty((P, 2, geo.NL + 1, 4))
    Y = xp.empty((P, 2, geo.ncl + 1, 4))
    specs_all, heat, meta = [], [], []
    for (j, (ci, sh)) in inst:
        y, pz = jobs[j]
        sp = shell_and_y_specs(geo, rng, 32, 8, [ci, ci], ci, sh, thetas=th)
        Uj, Yj = build_pairs(be, geo, confs, a.kappa, sp, y, rng)
        k = len(specs_all)
        U[k:k + len(sp)] = Uj
        Y[k:k + len(sp)] = Yj
        heat += list(range(k + len(sp) // 2, k + len(sp)))
        specs_all += sp
        meta.append(dict(job=j, yclass=y, pool=pz, conf=ci, shift=list(sh), first_pair=k))
        del Uj, Yj
    U = heat_start(be, geo, a.beta, U, Y, heat, sampler=smp)
    sync(be)
    t_build = time.time() - t1
    # lever snapshots: chain A box links of the first 8 pairs of each start of each job, at T/2 and at the end
    pick = []
    for m in meta:
        pick += list(range(m["first_pair"], m["first_pair"] + 8)) + list(range(m["first_pair"] + 40, m["first_pair"] + 48))
    pick_d = xp.asarray(pick)
    snaps = {}

    def grab(S, tag):
        snaps[tag] = cp.asnumpy(S.U[pick_d, 0][:, geo.dyn_d]).astype(np.float32) if be.gpu else \
            np.asarray(S.U[pick, 0][:, geo.dyn_lids]).astype(np.float32)

    half = max(1, a.T // 2)
    t2 = time.time()
    r = run_chains(be, geo, a.beta, a.kappa, U, Y, a.T, a.every, deadline=deadline, sampler=smp,
                   snap={half: lambda S: grab(S, "mid")})
    grab(r["S"], "end")
    sync(be)
    t_main = time.time() - t2
    done = r["sweeps_done"]
    acc = r["S"].acceptance() if hasattr(r["S"], "acceptance") else None
    Yh = cp.asnumpy(Y[:, 0]) if be.gpu else np.asarray(Y[:, 0])
    Y_inst = np.stack([Yh[m["first_pair"]] for m in meta]).astype(np.float32)
    np.savez_compressed(a.out.replace(".json", ".npz"),
                        d=r["d"].astype(np.int32), w=r["w"].astype(np.float32), plaq=r["plaq"].astype(np.float32),
                        specs=np.array([(s_[0], s_[1], *s_[2], 1 if s_[3] == "z" else (2 if s_[3] == "y" else 0), s_[4], s_[5])
                                        for s_ in specs_all], dtype=np.float64),
                        Y_inst=Y_inst, snap_mid=snaps.get("mid", np.zeros(0, np.float32)), snap_end=snaps["end"],
                        snap_pairs=np.array(pick), dyn_lids=geo.dyn_lids, shell=geo.shell)
    out = dict(beta=a.beta, ell=a.ell, kappa=a.kappa, T=a.T, every=a.every, jobs=a.jobs, fused=a.fused, pairs=P,
               pool_pairs=sum(jobs[j][1] * 8 for j in pool_jobs), pool_T=Tp, seconds_geometry=t_geo, seconds_pool=t_pool,
               seconds_build=t_build, seconds_main=t_main, sweeps_done=done, capped=done < a.T,
               sec_per_sweep_main=t_main / done, seconds_total=time.time() - t_start,
               seconds_full_T_extrapolated=t_geo + t_pool + t_build + t_main / done * a.T, mh_acceptance=acc,
               plaq_mean=float(r["plaq"].mean()), d_end_mean=float(r["d"][-1].mean()), n_box_links=int(len(geo.dyn_lids)),
               klow_pool={str(k_): v for k_, v in klow_pool.items()}, instances=meta,
               npz=a.out.replace(".json", ".npz"))
    if be.gpu:
        out["gpu_pool_bytes"] = int(cp.get_default_memory_pool().total_bytes())
    json.dump(out, open(a.out, "w"), indent=1)
    print(json.dumps({k_: out[k_] for k_ in ("beta", "T", "jobs", "pairs", "sweeps_done", "capped", "seconds_pool",
                                              "seconds_build", "seconds_main", "seconds_total", "sec_per_sweep_main",
                                              "seconds_full_T_extrapolated", "mh_acceptance", "plaq_mean")}))


# ====================================================================================================================== selftest

def cmd_selftest(a):
    be = Backend(a.gpu, 7)
    xp = be.xp
    ok = True
    # (0) quaternion product against 2x2 matrices (the gpu/gauge.py layout)
    q = np.random.default_rng(1).standard_normal((2, 4))
    q /= np.linalg.norm(q, axis=-1, keepdims=True)

    def q2m(v):
        return np.array([[v[0] + 1j * v[3], v[2] + 1j * v[1]], [-v[2] + 1j * v[1], v[0] - 1j * v[3]]])
    mm = q2m(q[0]) @ q2m(q[1])
    qq = be.qmul(xp.asarray(q[0]), xp.asarray(q[1]))
    qq = xp.asnumpy(qq) if be.gpu else qq
    e0 = float(np.abs(q2m(qq) - mm).max())
    print("qmul vs matrices:", e0)
    ok &= e0 < 1e-12
    # (a) normaliser against quadrature
    from scipy.integrate import quad
    worst = 0.0
    for av in (0.0, 0.1, 1.0, 5.0, 30.0, 120.0):
        ref = quad(lambda th: (2 / np.pi) * np.sin(th) ** 2 * np.exp(av * np.cos(th)), 0, np.pi, epsabs=0, epsrel=1e-13)[0]
        v = float(be.log_z(xp.asarray([av]))[0])
        worst = max(worst, abs(v - math.log(ref)))
    print("log z vs quadrature, worst abs error:", worst)
    ok &= worst < 1e-9
    # (b) x0 law against the exact CDF (KS) for several alpha
    from scipy.stats import kstest
    for al in (0.05, 0.5, 3.0, 20.0):
        x = be.sample_x0(xp.full(40000, al))
        x = xp.asnumpy(x) if be.gpu else x
        grid = np.linspace(-1, 1, 20001)
        dens = np.sqrt(np.maximum(0, 1 - grid ** 2)) * np.exp(al * (grid - 1))
        cdf = np.cumsum(dens)
        cdf /= cdf[-1]
        p = kstest(x, lambda t: np.interp(t, grid, cdf)).pvalue
        print(f"x0 KS alpha={al}: p = {p:.3f}")
        ok &= p > 1e-3
    # (b') maximal coupling: marginal of q2 has the law of F2 (mean of q2 . n2 against the exact value)
    F1 = xp.asarray(np.tile([2.0, 0.5, 0.0, 0.0], (40000, 1)))
    F2 = xp.asarray(np.tile([1.5, 0.0, 1.0, 0.0], (40000, 1)))
    q1, q2 = be.coupled_vmf(F1, F2)
    a2 = float(np.linalg.norm([1.5, 0, 1.0, 0]))
    m2 = float(xp.mean(xp.sum(q2 * F2, axis=-1)) / a2)
    ref = quad(lambda th: np.sin(th) ** 2 * np.cos(th) * np.exp(a2 * np.cos(th)), 0, np.pi)[0] / \
        quad(lambda th: np.sin(th) ** 2 * np.exp(a2 * np.cos(th)), 0, np.pi)[0]
    same = float(xp.mean(xp.all(q1 == q2, axis=-1)))
    print(f"coupling: <q2.n2> = {m2:.4f} (exact {ref:.4f}), P(q1 = q2) = {same:.3f}")
    ok &= abs(m2 - ref) < 0.01
    # (c) G1: identical boundaries and Y give zero disagreement; (d) chain at kappa = 0 and kappa = 16 keeps the box
    # plaquette at the equilibrium value of the outside (stationarity of the conditional law, Y sampled given U0)
    if a.conf:
        confs, beta = load_confs(a.conf)
        geo = Geometry(4)
        geo.to_device(xp)
        rng = np.random.default_rng(3)
        specs = [(0, 0, (0, 0, 0, 0), "none", 0, 0.0), (0, 0, (5, 1, 2, 9), "none", 0, 0.0),
                 (1, 1, (3, 3, 0, 4), "none", 0, 0.0)]
        for kappa in (0.0, 16.0):
            U, Y = build_pairs(be, geo, confs, kappa, specs, "sampled", rng)
            S0 = PairSampler(be, geo, beta, kappa, U.copy(), Y)
            p0 = float(S0.plaquettes().mean())
            r = run_chains(be, geo, beta, kappa, U, Y, 60, 10)
            dmax = int(r["d"].max())
            print(f"kappa={kappa}: G1 max disagreement = {dmax}; box plaquette start {p0:.4f}, run mean {r['plaq'].mean():.4f}")
            ok &= dmax == 0
    if a.conf:
        ok &= selftest_onelink(be, a.conf)
        ok &= selftest_gauge(be, a.conf)
    print("SELFTEST", "OK" if ok else "FAILED")


def selftest_onelink(be, conf, beta_k=(None, 16.0), R=96, upd=40, N=40000, sampler=None):
    """(d) exactness of the constrained update on one link: everything else frozen; the chain mean of the link (R replicas,
    `upd` updates each after 10 burn-in) against the exact conditional mean by importance sampling over Haar."""
    xp = be.xp
    confs, beta = load_confs(conf)
    kappa = beta_k[1]
    geo = Geometry(2)
    best = None
    for ci, c in enumerate(geo.classes):
        for i in range(len(c["lid"])):
            ne = int(c["e_mask"][i].sum())
            if best is None or ne > best[2]:
                best = (ci, i, ne)
    ci, i, ne = best
    geo.classes = [{k: v[i:i + 1] for k, v in geo.classes[ci].items()}]
    geo.to_device(xp)
    c = geo.classes[0]
    lid = int(c["lid"][0])
    rng = np.random.default_rng(5)
    U, Y = build_pairs(be, geo, confs, kappa, [(0, 0, (1, 2, 3, 4), "none", 0, 0.0)], "sampled", rng)
    U = xp.broadcast_to(U, (R,) + U.shape[1:]).copy()
    Y = xp.broadcast_to(Y, (R,) + Y.shape[1:]).copy()
    S = (sampler or PairSampler)(be, geo, beta, kappa, U, Y)
    acc = []
    for t in range(10 + upd):
        S.update_class(c)
        if t >= 10:
            acc.append(S.U[:, 0, lid].copy())
    A = xp.stack(acc)                                                   # (upd, R, 4)
    m_chain = A.mean(axis=(0, 1))
    se = A.mean(axis=0).std(axis=0) / math.sqrt(R)                     # replica means are independent
    q = xp.asarray(np.random.default_rng(1).standard_normal((N, 4)))
    q = q / xp.linalg.norm(q, axis=-1, keepdims=True)
    U1 = S.U[:1, :1].copy()
    logw = xp.zeros(N)
    B = 50
    for s0 in range(0, N, B):
        Ub = xp.broadcast_to(U1, (B,) + U1.shape[1:]).copy()
        Ub[:, 0, lid] = q[s0:s0 + B]
        T = PairSampler(be, geo, beta, kappa, Ub, xp.broadcast_to(Y[:1, :1], (B, 1) + Y.shape[2:]).copy())
        W = xp.sum(T.prod(c["stp"], c["stpd"]), axis=-2)[:, 0, 0]
        ph = T.phi(c["e_l"])[:, 0, 0]
        yl = T.Y[:, 0, c["e_l"][0]]
        lin = xp.sum(ph * yl, axis=-1)
        lz = be.log_z(kappa * xp.linalg.norm(ph, axis=-1))
        logw[s0:s0 + B] = beta * xp.sum(q[s0:s0 + B] * (W * be.conj), axis=-1) + xp.sum(c["e_mask"][0] * (kappa * lin - lz), axis=-1)
    w = xp.exp(logw - logw.max())
    m_ex = (w[:, None] * q).sum(axis=0) / w.sum()
    ess = float(w.sum() ** 2 / (w ** 2).sum())
    se_ex = xp.sqrt(((w[:, None] * (q - m_ex)) ** 2).sum(axis=0)) / w.sum()
    z = xp.abs(m_chain - m_ex) / xp.sqrt(se ** 2 + se_ex ** 2)
    zmax = float(z.max())
    tohost = (lambda v: xp.asnumpy(v)) if be.gpu else (lambda v: np.asarray(v))
    print(f"(d) one link ({ne} constraint entries), kappa={kappa}: chain {np.round(tohost(m_chain), 4)} exact "
          f"{np.round(tohost(m_ex), 4)} (ESS {ess:.0f}); max |z| = {zmax:.2f}")
    return zmax < 4.0


def selftest_gauge(be, conf, sweeps=40, P=6, sampler=None):
    """G0: a random gauge transformation of the whole frame (box links, outside links, block variables at their coarse end
    points) leaves the box plaquette expectation unchanged (covariance of the constrained law). Same random numbers are
    not shared, so the comparison is statistical."""
    xp = be.xp
    confs, beta = load_confs(conf)
    geo = Geometry(2)
    geo.to_device(xp)
    rng = np.random.default_rng(8)
    specs = [(i % confs.shape[0], i % confs.shape[0], tuple(int(v) for v in rng.integers(0, 16, 4)), "none", 0, 0.0)
             for i in range(P)]
    U, Y = build_pairs(be, geo, confs, 16.0, specs, "sampled", rng)
    Uh = xp.asnumpy(U) if be.gpu else np.asarray(U)
    Yh = xp.asnumpy(Y) if be.gpu else np.asarray(Y)
    g = rng.standard_normal((geo.F ** 4, 4))
    g /= np.linalg.norm(g, axis=-1, keepdims=True)
    Ug, Yg = gauge_transform(geo, Uh, Yh, g)
    p0 = float(PairSampler(be, geo, beta, 16.0, xp.asarray(Uh), xp.asarray(Yh)).plaquettes().mean())
    p1 = float(PairSampler(be, geo, beta, 16.0, xp.asarray(Ug), xp.asarray(Yg)).plaquettes().mean())
    r0 = run_chains(be, geo, beta, 16.0, xp.asarray(Uh), xp.asarray(Yh), sweeps, 5, align=False, sampler=sampler)
    r1 = run_chains(be, geo, beta, 16.0, xp.asarray(Ug), xp.asarray(Yg), sweeps, 5, align=False, sampler=sampler)
    a0, a1 = r0["plaq"].mean(axis=(1, 2)), r1["plaq"].mean(axis=(1, 2))   # per pair
    diff = a1 - a0
    zz = abs(diff.mean()) / (diff.std(ddof=1) / math.sqrt(len(diff)) + 1e-12)
    print(f"G0 gauge covariance: start plaquette {p0:.6f} vs transformed {p1:.6f}; run means {a0.mean():.4f} vs "
          f"{a1.mean():.4f}, |z| = {zz:.2f}")
    return abs(p0 - p1) < 1e-10 and zz < 3.0


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("selftest")
    s.add_argument("--gpu", action="store_true")
    s.add_argument("--conf", default="")
    s = sub.add_parser("gen")
    s.add_argument("beta", type=float)
    s.add_argument("nconf", type=int)
    s.add_argument("seed", type=int)
    s.add_argument("out")
    s.add_argument("--therm", type=int, default=300)
    s = sub.add_parser("pilot")
    s.add_argument("conf")
    s.add_argument("beta", type=float)
    s.add_argument("ell", type=int)
    s.add_argument("kappa", type=float)
    s.add_argument("sweeps", type=int)
    s.add_argument("out")
    s.add_argument("--pairs", type=int, default=4)
    s.add_argument("--every", type=int, default=10)
    s.add_argument("--seed", type=int, default=11)
    s.add_argument("--gpu", action="store_true")
    s = sub.add_parser("job")
    s.add_argument("conf")
    s.add_argument("beta", type=float)
    s.add_argument("ell", type=int)
    s.add_argument("kappa", type=float)
    s.add_argument("yclass")
    s.add_argument("T", type=int)
    s.add_argument("out")
    s.add_argument("--pool", type=int, default=8)
    s.add_argument("--batch", type=int, default=1)
    s.add_argument("--max_seconds", type=float, default=0.0, help="hard cap on the whole job (0 = none)")
    s.add_argument("--force", action="store_true", help="skip the idle-GPU check")
    s.add_argument("--every", type=int, default=10)
    s.add_argument("--seed", type=int, default=13)
    s.add_argument("--gpu", action="store_true")
    s = sub.add_parser("launch")
    s.add_argument("conf")
    s.add_argument("beta", type=float)
    s.add_argument("T", type=int)
    s.add_argument("jobs", help='comma list of class:pool, e.g. "A3:8,A1:8,A2:0,A4:0,A6:0,sampled:0"')
    s.add_argument("out")
    s.add_argument("--ell", type=int, default=6)
    s.add_argument("--kappa", type=float, default=16.0)
    s.add_argument("--every", type=int, default=10)
    s.add_argument("--seed", type=int, default=17)
    s.add_argument("--max_seconds", type=float, default=0.0)
    s.add_argument("--gpu", action="store_true")
    s.add_argument("--fused", action="store_true")
    s.add_argument("--force", action="store_true")
    a = ap.parse_args()
    dict(selftest=cmd_selftest, gen=cmd_gen, pilot=cmd_pilot, job=cmd_job, launch=cmd_launch)[a.cmd](a)


if __name__ == "__main__":
    main()
