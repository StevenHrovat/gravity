"""c9b option B: the low-rank-exact kinetic term for constrained HMC (PILOT2.md "Options"; owner: "Yes, build B").

Kinetic matrix on the fine Lie-algebra space (3 components per dynamic fine link):
    M = 1 + kappa_c J0^T J0,
with J0 the Jacobian of the constrained block variables (coarse R^4 per constrained coarse link) at the run's start configuration, fixed
during the run, so HMC stays exact. Then:
- momentum draw: p = xi + sqrt(kappa_c) J0^T eta (xi, eta standard normal on the fine / coarse space), so Cov p = M exactly;
- velocity: M^-1 p = p - kappa_c J0^T (1 + kappa_c J0 J0^T)^-1 J0 p (Woodbury), the coarse solve by conjugate gradients with a
  per-link (Jacobi-block) preconditioner 1/(1 + kappa_c s_y), s_y = tr((J0 J0^T)_yy)/3 from Hutchinson probes;
- kinetic energy: (1/2) p . M^-1 p.
J0 x (forward mode) is computed by tangent propagation through the same strided blocking as ir_constrained.coarse_links_strided;
J0^T r (reverse mode) by its tape. Their consistency is a selftest (dot test).

CLI
  py ir_lowrank.py selftest                     seconds: dot test, M^-1 M = 1, momentum covariance, leapfrog reversibility, dH ~ eps^2
  py ir_lowrank.py cgcount --go ...             the data-free CG iteration count (PILOT2.md; one background, no sampling)
  py ir_lowrank.py agree --go ...               agreement with the current sampler on a small lattice (selftest-level run)
  py ir_lowrank.py tune --go ...                the T-B' repeat with option B (PREREG-PILOT2.md addition)
"""
import argparse
import importlib.util
import json
import math
import os
import sys
import time

import numpy as np

import ir_constrained as ic
from ir_constrained import qmul, qdag, ev, vadd, transverse, Tape, coarse_links_strided

HERE = os.path.dirname(os.path.abspath(__file__))


# ------------------------------------------------------------------------------------------------------------ forward mode (J0 x)
def _take(x, off, stride):
    M = x.shape[2]
    m = M // stride
    idx = [(off[i] + stride * np.arange(m)) % M for i in range(4)]
    return x[(slice(None), slice(None), idx[0][:, None, None, None], idx[1][None, :, None, None],
              idx[2][None, None, :, None], idx[3][None, None, None, :])]


def _smear_dual(F, dF, w):
    """smear_step_strided on (value, tangent) pairs."""
    def at(x, off):
        return _take(x, off, 2)
    outV, outT = [], []
    for mu in range(4):
        o = [0, 0, 0, 0]

        def prod(*pairs):
            v, t = pairs[0]
            for v2, t2 in pairs[1:]:
                t = qmul(t, v2) + qmul(v, t2)
                v = qmul(v, v2)
            return v, t

        def P(nu, off, conj=False):
            v, t = at(F[nu], off), at(dF[nu], off)
            return (qdag(v), qdag(t)) if conj else (v, t)
        sv, st = prod(P(mu, o), P(mu, ev(mu, 1)))
        for nu in transverse(mu):
            uv, ut = prod(P(nu, o), P(mu, ev(nu, 1)), P(mu, vadd(ev(nu, 1), ev(mu, 1))), P(nu, ev(mu, 2), True))
            dv, dt = prod(P(nu, ev(nu, -1), True), P(mu, ev(nu, -1)), P(mu, vadd(ev(nu, -1), ev(mu, 1))), P(nu, vadd(ev(nu, -1), ev(mu, 2))))
            sv, st = sv + w * (uv + dv), st + w * (ut + dt)
        n = np.sqrt((sv * sv).sum(axis=0, keepdims=True))
        q = sv / n
        outV.append(q)
        outT.append((st - (q * st).sum(axis=0, keepdims=True) * q) / n)
    return outV, outT


def jvp(U, X, n, w):
    """J0 x: tangent of the level-n block variables (4 mu, 4, B, Nc^4) for the fine Lie vector X (4 mu, 3, B, N^4) (delta U = x U)."""
    F = [U[mu] for mu in range(4)]
    dF = [qmul(np.concatenate([np.zeros_like(X[mu][:1]), X[mu]]), U[mu]) for mu in range(4)]
    for _ in range(n):
        F, dF = _smear_dual(F, dF, w)
    return np.stack(F), np.stack(dF)


def vjp(U, R, n, w):
    """J0^T r: the fine Lie vector Im(G U^dagger), G = d<r, V>/dU (r: coarse R^4 per link)."""
    T = Tape(np)
    L = [T.leaf(U[mu]) for mu in range(4)]
    V = coarse_links_strided(T, L, n, w) if n > 0 else L
    T.backward([(V[mu], R[mu]) for mu in range(4)])
    G = np.stack([L[mu].grad if L[mu].grad is not None else np.zeros_like(U[mu]) for mu in range(4)])
    rest = tuple(range(2, G.ndim))
    return qmul(G.transpose(1, 0, *rest), qdag(U.transpose(1, 0, *rest)))[1:].transpose(1, 0, *rest)


# ------------------------------------------------------------------------------------------------------------ the kinetic operator
class LowRankKinetic:
    """M = 1 + kappa J0^T J0 on the dynamic fine links; J0 restricted to the constrained coarse links (cmask) and dynamic fine links (dyn)."""

    def __init__(self, U0, n, w, kappa, cmask, dyn, nprobe, rng, tol=1e-12, maxit=500):
        self.U0, self.n, self.w, self.kappa, self.cmask, self.dyn = U0, n, w, kappa, cmask, dyn
        self.tol, self.maxit = tol, maxit
        self.cg_iters = []
        # Jacobi-block preconditioner: s_y = tr((J J^T)_yy)/3 by Hutchinson probes on the coarse space
        acc = np.zeros_like(cmask)
        for _ in range(nprobe):
            r = rng.normal(size=cmask.shape[:1] + (4,) + cmask.shape[2:]) * cmask
            acc = acc + (r * self.JJt(r)).sum(axis=1, keepdims=True)
        self.s = acc / nprobe / 3
        # tangent-only Jacobi-block preconditioner (the radial direction of each V_y is outside the range of J; there A = 1)
        self.V0 = coarse_links_strided(Tape(np), [Tape(np).leaf(U0[mu]) for mu in range(4)], n, w) if n > 0 else None
        self.V0 = np.stack([v.val for v in self.V0]) if self.V0 is not None else U0
        self.fac = cmask / (1 + kappa * self.s) + (1 - cmask)
        self.pinv = None

    def prec(self, r):
        if self.pinv is not None:  # override (plain CG: ones)
            return self.pinv * r
        rad = (r * self.V0).sum(axis=1, keepdims=True) * self.V0
        return rad + (r - rad) * self.fac

    def J(self, X):
        return jvp(self.U0, X * self.dyn, self.n, self.w)[1] * self.cmask

    def Jt(self, R):
        return vjp(self.U0, R * self.cmask, self.n, self.w) * self.dyn

    def JJt(self, R):
        return self.J(self.Jt(R))

    def A(self, Z):
        return Z + self.kappa * self.JJt(Z)

    def solve(self, b):
        """(1 + kappa J J^T) z = b by preconditioned CG (relative tolerance tol)."""
        x = np.zeros_like(b)
        r = b.copy()
        z = self.prec(r)
        p = z.copy()
        rz = (r * z).sum()
        bn = math.sqrt((b * b).sum()) or 1.0
        for k in range(1, self.maxit + 1):
            Ap = self.A(p)
            alpha = rz / (p * Ap).sum()
            x = x + alpha * p
            r = r - alpha * Ap
            if math.sqrt((r * r).sum()) < self.tol * bn:
                self.cg_iters.append(k)
                return x
            z = self.prec(r)
            rz_new = (r * z).sum()
            p = z + (rz_new / rz) * p
            rz = rz_new
        self.cg_iters.append(self.maxit + 1)  # did not converge within maxit
        return x

    def velocity(self, P):
        P = P * self.dyn
        return P - self.kappa * self.Jt(self.solve(self.J(P)))

    def sample(self, rng, shape_fine):
        xi = rng.normal(size=shape_fine) * self.dyn
        eta = rng.normal(size=self.cmask.shape[:1] + (4,) + self.cmask.shape[2:]) * self.cmask
        return xi + math.sqrt(self.kappa) * self.Jt(eta)

    def M_apply(self, X):
        X = X * self.dyn
        return X + self.kappa * self.Jt(self.J(X))


def leapfrog_lr(model, K, U, P, eps, nleap):
    S, f = model.force(U)
    P = P - 0.5 * eps * f
    for k in range(nleap):
        U = ic.qexp_left(K.velocity(P), U, eps)
        S, f = model.force(U)
        P = P - (eps if k < nleap - 1 else 0.5 * eps) * f
    return U, P, S


def hmc_step_lr(model, K, U, eps, nleap, rng):
    P = K.sample(rng, (4, 3) + U.shape[2:])
    S0, _ = model.evaluate(U, need_grad=False)
    H0 = 0.5 * (P * K.velocity(P)).sum() + S0[0]
    U1, P1, S1 = leapfrog_lr(model, K, U, P, eps, nleap)
    H1 = 0.5 * (P1 * K.velocity(P1)).sum() + S1[0]
    dH = H1 - H0
    acc = rng.random() < math.exp(min(0.0, -dH))
    return (U1 if acc else U), acc, dH


# ------------------------------------------------------------------------------------------------------------ helpers
def setup(N, n, beta, kappa, B, rng, U=None, R=9):
    m = ic.Model(N, n, 2.0, ic.coupling("wilson", beta), kappa=kappa, lean=True)
    if U is None:
        U = ic.random_su2((4, B) + (N,) * 4, rng).transpose(1, 0, 2, 3, 4, 5, 6)
    m.target = m.coarse(U).copy()
    m.cmask, m.dyn = ic.masks(m, B, (0, 0, 0, 0), 1, R)
    return m, U


def background(N, beta, npre, bgseed):
    spec = importlib.util.spec_from_file_location("goodblock", os.path.join(HERE, "..", "c3b-refit", "goodblock.py"))
    gb = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gb)
    upd = gb.BL.make_updater("su2", gb.BL.PeriodicBox(N), beta, 1, bgseed, False, False)
    for _ in range(npre):
        upd.sweep(3)
    return np.stack([np.asarray(u) for u in gb.chain_q("su2", np, upd, 0)])


# ------------------------------------------------------------------------------------------------------------ selftest
def selftest(_a):
    rng = np.random.default_rng(11)
    ok = True
    m, U = setup(4, 1, 0.5, 10.0, 1, rng)
    # 1. jvp against finite differences of the block variables
    X = rng.normal(size=(4, 3, 1) + (4,) * 4)
    h = 1e-6
    Vp = m.coarse(ic.qexp_left(X, U, h))
    Vm = m.coarse(ic.qexp_left(X, U, -h))
    fd = (Vp - Vm) / (2 * h)
    tan = jvp(U, X, 1, 2.0)[1]
    e = float(np.abs(fd - tan).max() / np.abs(tan).max())
    print(f"J x (tangent propagation) vs finite differences of the block variables: relative {e:.1e}")
    ok &= e < 1e-7
    # 2. dot test <r, J x> = <J^T r, x>
    r = rng.normal(size=(4, 4, 1) + (2,) * 4)
    lhs = float((r * tan).sum())
    rhs = float((vjp(U, r, 1, 2.0) * X).sum())
    print(f"dot test <r, J x> = <J^T r, x>: {lhs:.12f} vs {rhs:.12f}")
    ok &= abs(lhs - rhs) < 1e-10 * max(1, abs(lhs))
    # 3. M^-1 M = 1 through the CG / Woodbury path
    K = LowRankKinetic(U, 1, 2.0, 10.0, m.cmask, m.dyn, 8, rng)
    Y = rng.normal(size=(4, 3, 1) + (4,) * 4) * m.dyn
    back = K.velocity(K.M_apply(Y))
    e3 = float(np.abs(back - Y).max() / np.abs(Y).max())
    print(f"M^-1 M Y = Y (Woodbury + CG, tol 1e-12): relative {e3:.1e}; CG iterations {K.cg_iters[-1]}")
    ok &= e3 < 1e-9
    # 4. momentum covariance: mean of p.M^-1 p = dimension (chi^2)
    dim = int(3 * m.dyn.sum())
    q = [float((p * K.velocity(p)).sum()) for p in (K.sample(rng, Y.shape) for _ in range(40))]
    z = (np.mean(q) - dim) / math.sqrt(2 * dim / 40)
    print(f"momentum draw: mean p.M^-1 p over 40 draws {np.mean(q):.1f} vs dimension {dim} (z = {z:.2f})")
    ok &= abs(z) < 4
    # 5. leapfrog reversibility and dH ~ eps^2 with the low-rank kinetic term
    P = K.sample(rng, Y.shape)
    U1, P1, _ = leapfrog_lr(m, K, U, P, 0.02, 10)
    U2, _, _ = leapfrog_lr(m, K, U1, -P1, 0.02, 10)
    rv = float(np.abs(U2 - U).max())
    print(f"leapfrog with M = 1 + kappa J^T J reversible: {rv:.1e}")
    ok &= rv < 1e-8
    dHs = []
    for eps in (0.02, 0.01):
        S0, _ = m.evaluate(U, need_grad=False)
        Ue, Pe, Se = leapfrog_lr(m, K, U, P, eps, int(round(0.4 / eps)))
        dHs.append(abs(0.5 * (Pe * K.velocity(Pe)).sum() + Se[0] - 0.5 * (P * K.velocity(P)).sum() - S0[0]))
    ratio = dHs[0] / max(dHs[1], 1e-300)
    print(f"|dH| at eps 0.02, 0.01: {dHs[0]:.2e}, {dHs[1]:.2e} (ratio {ratio:.1f}; leapfrog: about 4; eps 0.04 is pre-asymptotic on this hot start)")
    ok &= 2.5 < ratio < 6
    print("SELFTEST", "OK" if ok else "FAIL")
    return 0 if ok else 1


# ------------------------------------------------------------------------------------------------------------ CG count (data-free)
def cgcount(a):
    if not a.go:
        print("cgcount runs only with --go (PILOT2.md: the data-free CG count, owner-approved)."); return 2
    rng = np.random.default_rng(a.seed)
    out = {"rows": []}
    for spec in a.settings.split(";"):
        N, n = (int(v) for v in spec.split(","))
        t0 = time.time()
        U = background(N, a.beta, a.npre, a.bgseed)
        m, U = setup(N, n, a.beta, a.kappa, 1, rng, U=U, R=2)
        K = LowRankKinetic(U, n, 2.0, a.kappa, m.cmask, m.dyn, a.nprobe, rng, tol=a.tol)
        t_pre = time.time() - t0
        its_pc, its_plain, t_solve = [], [], []
        for _ in range(a.nrhs):
            b = K.J(K.sample(rng, (4, 3, 1) + (N,) * 4))  # the right-hand side met in velocity(): J p
            t1 = time.time()
            K.solve(b)
            t_solve.append(time.time() - t1)
            its_pc.append(K.cg_iters[-1])
            K.pinv = np.ones_like(m.cmask)
            K.solve(b)
            its_plain.append(K.cg_iters[-1])
            K.pinv = None
        # cost of one J and one J^T against one force evaluation
        X = rng.normal(size=(4, 3, 1) + (N,) * 4)
        t1 = time.time(); K.J(X); tj = time.time() - t1
        r = rng.normal(size=m.cmask.shape[:1] + (4,) + m.cmask.shape[2:]) * m.cmask
        t1 = time.time(); K.Jt(r); tjt = time.time() - t1
        t1 = time.time(); m.force(U); tf = time.time() - t1
        row = {"N": N, "n": n, "b": 2 ** n, "kappa": a.kappa, "cg_iters_precond": its_pc, "cg_iters_plain": its_plain,
               "s_solve": float(np.median(t_solve)), "s_J": tj, "s_Jt": tjt, "s_force": tf,
               "c_blk": (tj + tjt) / 2 / tf, "per_step_factor": 1 + (tj + tjt) * (np.median(its_pc) + 1) / tf,
               "s_y_median": float(np.median(K.s[m.cmask > 0])), "t_setup_s": t_pre}
        out["rows"].append(row)
        print(json.dumps(row), flush=True)
    json.dump(out, open(a.out, "w"), indent=1)
    return 0


# ------------------------------------------------------------------------------------------------------------ agreement (small lattice)
def agree(a):
    """Option B and the current (diagonal-mass) sampler on the same small constrained system: the means of V_x components squared
    and of S per link must agree within errors (a selftest-level run, no physics number)."""
    if not a.go:
        print("agree runs only with --go."); return 2
    rng = np.random.default_rng(a.seed)
    U0 = background(a.N, a.beta, 20, a.bgseed)
    res = {}
    for name in ("diag", "lowrank"):
        m, U = setup(a.N, a.n, a.beta, a.kappa, 1, rng, U=U0.copy(), R=2)
        if name == "diag":
            m.mass = m.precond_mass(U, 16, rng)
        else:
            K = LowRankKinetic(U, a.n, 2.0, a.kappa, m.cmask, m.dyn, 8, rng)
        obs, accs = [], []
        for k in range(a.ntraj):
            if name == "diag":
                U, acc, _ = ic.hmc_step(m, U, a.eps_diag, a.nleap_diag, rng)
                acc = bool(np.mean(acc) > 0.5)
            else:
                U, acc, _ = hmc_step_lr(m, K, U, a.eps_lr, a.nleap_lr, rng)
            accs.append(acc)
            V = m.coarse(U)
            vx = V[(1, slice(None), 0) + (0, 0, 0, 0)]
            obs.append([vx[0] ** 2, vx[1] ** 2 + vx[2] ** 2 + vx[3] ** 2, float(m.evaluate(U, False)[0][0]) / (6 * a.N ** 4)])
        obs = np.array(obs)[a.ntraj // 5:]
        blk = np.array_split(obs, 10)
        mean = obs.mean(axis=0)
        err = np.std([b.mean(axis=0) for b in blk], axis=0, ddof=1) / math.sqrt(10)
        res[name] = {"mean": mean.tolist(), "err": err.tolist(), "acc": float(np.mean(accs))}
        print(json.dumps({name: res[name]}), flush=True)
    d = np.array(res["diag"]["mean"]) - np.array(res["lowrank"]["mean"])
    s = np.sqrt(np.array(res["diag"]["err"]) ** 2 + np.array(res["lowrank"]["err"]) ** 2)
    res["z"] = (d / s).tolist()
    print(json.dumps({"z (diag - lowrank)/sigma": res["z"]}))
    json.dump(res, open(a.out, "w"), indent=1)
    return 0


# ------------------------------------------------------------------------------------------------------------ tune (T-B' with B)
def tune(a):
    if not a.go:
        print("tune runs only with --go (PREREG-PILOT2.md, the option-B addition)."); return 2
    t_start = time.time()
    prog = open(a.out + ".progress.jsonl", "w", buffering=1)
    out = {"setting": {k: v for k, v in vars(a).items() if k != "func"}, "stopped": None}

    def note(**kw):
        kw["elapsed"] = round(time.time() - t_start, 1)
        prog.write(json.dumps(kw) + "\n")

    def save():
        out["wall_s"] = time.time() - t_start
        json.dump(out, open(a.out, "w"), indent=1)

    def over():
        return time.time() - t_start > a.max_wall
    rng = np.random.default_rng(a.seed)
    U0 = background(a.N, a.beta, a.npre, a.bgseed)
    out["t_background_s"] = time.time() - t_start
    note(stage="background done")
    m, U = setup(a.N, a.n, a.beta, a.kappa, 1, rng, U=U0, R=a.R)
    t0 = time.time()
    K = LowRankKinetic(U, a.n, 2.0, a.kappa, m.cmask, m.dyn, a.nprobe, rng, tol=a.tol)
    out["t_kinetic_setup_s"] = time.time() - t0
    import ir_condlaw as cl
    eps, nleap = a.eps, a.nleap
    out["tuning"] = []
    tuned = False
    for _ in range(a.tune_max):
        accs, ts, its = [], [], []
        for _ in range(a.tune_traj):
            t1 = time.time()
            n0 = len(K.cg_iters)
            U, acc, dH = hmc_step_lr(m, K, U, eps, nleap, rng)
            ts.append(time.time() - t1)
            its.extend(K.cg_iters[n0:])
            accs.append(float(acc))
            if over():
                break
        blk = {"eps": eps, "nleap": nleap, "acc": float(np.mean(accs)), "s_traj": float(np.median(ts)), "n": len(accs),
               "cg_median": float(np.median(its)) if its else None}
        out["tuning"].append(blk)
        note(stage="tune block", **blk)
        save()
        if over():
            break
        if blk["acc"] >= 0.6:
            tuned = True
            break
        eps, nleap = eps / 2, nleap * 2
    out.update(eps=eps, nleap=nleap)
    if not tuned:
        out["stopped"] = "stopped at max-wall during tuning" if over() else "tuning rule exhausted"
        save()
        return 0
    vx, S, accm, ts, its = [], [], [], [], []
    for k in range(a.n_meas):
        t1 = time.time()
        n0 = len(K.cg_iters)
        U, acc, _ = hmc_step_lr(m, K, U, eps, nleap, rng)
        ts.append(time.time() - t1)
        its.extend(K.cg_iters[n0:])
        accm.append(float(acc))
        V = m.coarse(U)
        vx.append(V[(1, slice(None), slice(None)) + (0, 0, 0, 0)].T.copy())
        S.append(float(m.evaluate(U, need_grad=False)[0][0]))
        if k % 10 == 9 or over():
            note(stage="measure", done=k + 1, acc=float(np.mean(accm)), s_traj=float(np.median(ts)))
        if over():
            break
    vxa = np.array(vx)
    out.update(acc_meas=float(np.mean(accm)), s_traj=float(np.median(ts)), n_meas=len(accm), cg_median=float(np.median(its)),
               tau_int_vx=float(np.nanmax([cl.tauint(vxa[:, c, i]) for c in range(vxa.shape[1]) for i in range(4)])),
               tau_int_S=cl.tauint(np.array(S)), status="done" if len(accm) == a.n_meas else "stopped at max-wall during measurement")
    print(json.dumps({k: v for k, v in out.items() if k != "setting"}), flush=True)
    note(stage="DONE")
    save()
    return 0


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest="cmd", required=True)
    sp.add_parser("selftest")
    c = sp.add_parser("cgcount")
    c.add_argument("--go", action="store_true")
    c.add_argument("--settings", default="12,2;24,3")
    c.add_argument("--beta", type=float, default=2.3)
    c.add_argument("--kappa", type=float, default=10.0)
    c.add_argument("--npre", type=int, default=20)
    c.add_argument("--nprobe", type=int, default=8)
    c.add_argument("--nrhs", type=int, default=3)
    c.add_argument("--tol", type=float, default=1e-10)
    c.add_argument("--seed", type=int, default=51)
    c.add_argument("--bgseed", type=int, default=5000)
    c.add_argument("--out", default="cgcount.json")
    g = sp.add_parser("agree")
    g.add_argument("--go", action="store_true")
    g.add_argument("--N", type=int, default=4)
    g.add_argument("--n", type=int, default=1)
    g.add_argument("--beta", type=float, default=2.3)
    g.add_argument("--kappa", type=float, default=10.0)
    g.add_argument("--ntraj", type=int, default=400)
    g.add_argument("--eps-diag", type=float, default=0.025)
    g.add_argument("--nleap-diag", type=int, default=20)
    g.add_argument("--eps-lr", type=float, default=0.05)
    g.add_argument("--nleap-lr", type=int, default=10)
    g.add_argument("--seed", type=int, default=61)
    g.add_argument("--bgseed", type=int, default=6000)
    g.add_argument("--out", default="agree_lowrank.json")
    t = sp.add_parser("tune")
    t.add_argument("--go", action="store_true")
    t.add_argument("--N", type=int, default=12)
    t.add_argument("--n", type=int, default=2)
    t.add_argument("--beta", type=float, default=2.3)
    t.add_argument("--kappa", type=float, default=10.0)
    t.add_argument("--R", type=int, default=2)
    t.add_argument("--npre", type=int, default=100)
    t.add_argument("--nprobe", type=int, default=8)
    t.add_argument("--tol", type=float, default=1e-10)
    t.add_argument("--eps", type=float, default=0.05)
    t.add_argument("--nleap", type=int, default=10)
    t.add_argument("--tune-traj", type=int, default=10)
    t.add_argument("--tune-max", type=int, default=6)
    t.add_argument("--n-meas", type=int, default=30)
    t.add_argument("--seed", type=int, default=43)
    t.add_argument("--bgseed", type=int, default=4002)
    t.add_argument("--max-wall", type=float, default=1500.0)
    t.add_argument("--out", default="pilot2_TBpB.json")
    a = ap.parse_args()
    return {"selftest": selftest, "cgcount": cgcount, "agree": agree, "tune": tune}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
