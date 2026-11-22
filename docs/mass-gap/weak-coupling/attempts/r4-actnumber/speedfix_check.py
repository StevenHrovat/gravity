"""Deterministic equivalence checks of the speed-fixed kernels against the array code / the earlier code (SPEEDFIX.md, check A).
Everything here is deterministic (no random stream involved), GPU, about 1 minute.  Usage: py speedfix_check.py"""
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cupy as cp  # noqa: E402
import actnumber as A  # noqa: E402
import actnumber_old as O  # noqa: E402  (the code as of the bench, kept unchanged as the reference)

rng = np.random.default_rng(23)
ok = []


def rep(name, good, detail):
    ok.append(bool(good))
    print(f"[{'PASS' if good else 'FAIL'}] {name}: {detail}", flush=True)


# 1. flux operators (APE smearing + Polyakov line) and plaquette field: GPU kernel vs the numpy array code, quaternion groups
for plane, Ls in (((0, 1), (6, 6, 6)), ((1, 2), (6, 6, 6)), ((0, 1), (4, 6, 8)), ((0, 2), (6, 4, 6))):
    geo = A.Geometry(None, 8, plane, Ls=Ls)
    U = A.hot_q(geo, 3, rng)
    lv = [0, 3, 8]
    ref = A.flux_ops(np, U, geo, "su2", lv)
    gpu = A.to_host(A.flux_ops(cp, [cp.asarray(u) for u in U], geo, "su2", lv))
    d = np.abs(ref - gpu).max()
    dp = 0.0
    for mu in range(4):
        for nu in range(mu + 1, 4):
            dp = max(dp, float(np.abs(A.plaquette_field(np, U, mu, nu, "su2") - A.to_host(A.plaquette_field(cp, [cp.asarray(u) for u in U], mu, nu, "su2"))).max()))
    rep(f"flux ops + plaquettes, plane {plane}, box {Ls}", d < 1e-13 and dp < 1e-13, f"max |flux op diff| {d:.1e}, max |plaquette diff| {dp:.1e}")

# 2. FusedSU2: overrelaxation sweeps (deterministic), new sheet kernel vs the earlier array-code fix-up, from one configuration
for Ls, plane in (((6, 6, 6), (0, 1)), ((8, 4, 6), (0, 1)), ((6, 6, 6), (1, 2))):
    geo = A.Geometry(None, 8, plane, xp=cp, Ls=Ls)
    geo_o = O.Geometry(None, 8, plane, xp=cp, Ls=Ls)
    U = A.hot_q(geo, 4, rng)
    new = A.FusedSU2(geo, 2.4, U, 1)
    old = O.FusedSU2(geo_o, 2.4, U, 1)
    dmax = 0.0
    for sweep in range(3):
        for mu in range(4):
            saved = old.fix.save(mu) if mu in (geo.a, geo.b) else None
            for p in (0, 1):
                new.pass_(mu, p, 1)
                old.g.update(mu, p, 1)
                if mu in (geo.a, geo.b):
                    old.fix.apply(mu, p, 1, saved)
                dmax = max(dmax, max(float(cp.abs(new.g.U[n] - old.g.U[n]).max()) for n in range(4)))
                for n in range(4):  # overrelaxation amplifies roundoff over passes: restart both from the earlier code's state every pass
                    new.g.U[n][...] = old.g.U[n]
    rep(f"FusedSU2 overrelaxation, new sheet kernel = earlier fix-up, box {Ls} plane {plane}", dmax < 1e-11, f"3 sweeps x 4 directions x 2 parities (per pass from a common state), max difference {dmax:.1e}")

# 3. U(1): overrelaxation pass (deterministic) kernel vs array code; Z2/U(1) heat bath is statistical (check B)
for Ls, plane in (((6, 6, 6), (0, 1)), ((4, 6, 8), (1, 2))):
    geo = A.Geometry(None, 8, plane, xp=cp, Ls=Ls)
    U = [rng.uniform(-np.pi, np.pi, (3,) + geo.dims) for _ in range(4)]
    ref = A.AbelianUpdater(geo, 1.1, U, 1, cp)
    new = A.GPUAbelian(geo, 1.1, U, 1)
    dmax = 0.0
    for sweep in range(3):
        for mu in range(4):
            for p in (0, 1):
                ref.pass_(mu, p, 1)
                new.pass_(mu, p, 1)
        d = max(float(cp.abs(cp.exp(1j * ref.U[n]) - cp.exp(1j * new.U[n])).max()) for n in range(4))
        dmax = max(dmax, d)
    rep(f"U(1) overrelaxation kernel = array code, box {Ls} plane {plane}", dmax < 1e-11, f"3 sweeps, max |exp(i theta) difference| {dmax:.1e}")

# 4. von Mises sampler of the kernel: one site, many chains -> distribution. Use the heat-bath of a free link: kappa from the staple of a
#    configuration with all other links 1 (cold) is 6 * beta; angle must follow exp(kappa cos(theta)).
import analyse_actnumber  # noqa: E402,F401
sys.path.insert(0, A.LATTICE)
import boundary as BD  # noqa: E402
geo = A.Geometry(2, 2, (0, 1), twisted=False, xp=cp)
nchain = 20000
U = [np.zeros((nchain,) + geo.dims) for _ in range(4)]
upd = A.GPUAbelian(geo, 0.4, U, 7)
th = []
for _ in range(4):
    upd.pass_(0, 0, 0)
    th.append(cp.asnumpy(upd.U[0][:, 0, 0, 0, 0]))   # site (0,0,0,0) has parity 0: updated; its staple is cold (all other links on the sites it reads are 1 only at the first pass)
th = np.concatenate(th[:1])  # first pass only: the staple of site 0 is exactly 6 (all neighbours cold)
kappa = 0.4 * 6
xs = np.linspace(-np.pi, np.pi, 40001)
D, pv = BD.ks_pvalue(th, BD.tab_cdf(xs, np.exp(kappa * (np.cos(xs) - 1))))
rep("U(1) heat-bath kernel: von Mises sampler (KS)", pv > 1e-3, f"KS p = {pv:.3f}, kappa = {kappa}, {th.size} draws")

print("CHECK A", "OK" if all(ok) else "FAILED", f"({sum(ok)}/{len(ok)})")
sys.exit(0 if all(ok) else 1)
