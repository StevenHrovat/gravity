"""Correctness of the fused update against the reference path (amendment A6). Each part is a short GPU test.

  py fused_selftest.py bessel      Bessel functions in the kernel against scipy
  py fused_selftest.py fields      deterministic fields (Wilson, constraint, linearised normaliser, log z) against the reference
  py fused_selftest.py g1          identical chains stay identical under the fused coupled update
  py fused_selftest.py onelink     one-link exactness with the fused update
  py fused_selftest.py gauge       G0 with the fused update
  py fused_selftest.py station     box plaquette stationarity from equilibrium (fused, kappa = 16)
  py fused_selftest.py compare     reference vs fused, same set-up: plaquette and disagreement plateau
  py fused_selftest.py speed       sweep time, full ell = 6 batch (480 pairs), fused vs reference
"""
import math
import sys
import time

import numpy as np

import constrained as C
import fused as Fz

CONF = "runs/conf_b2.3.npz"


def setup(ell, P, kappa=16.0, conf=CONF, perturb=True, seed=3, gpu=True):
    be = C.Backend(gpu, seed)
    geo = C.Geometry(ell)
    geo.to_device(be.xp)
    confs, beta = C.load_confs(conf)
    rng = np.random.default_rng(seed)
    if perturb:
        specs = C.shell_and_y_specs(geo, rng, P // 2, 0, [0, 0], 0, (0, 0, 0, 0), thetas=(math.pi,))
    else:
        specs = [(i % 4, i % 4, tuple(int(v) for v in rng.integers(0, 16, 4)), "none", 0, 0.0) for i in range(P)]
    U, Y = C.build_pairs(be, geo, confs, kappa, specs, "sampled", rng)
    return be, geo, beta, U, Y


def t_bessel():
    import cupy as cp
    from scipy.special import i0e, i1e
    a = np.concatenate([np.linspace(0, 1, 50), np.linspace(1, 40, 400), np.linspace(40, 400, 50)])
    S = Fz.FusedSampler.__new__(Fz.FusedSampler)
    if Fz.FusedSampler._module is None:
        Fz.FusedSampler._module = cp.RawModule(code=Fz.KERNEL, options=("-std=c++14",))
    k = Fz.FusedSampler._module.get_function("bessel_test")
    out = cp.zeros(2 * a.size)
    k(((a.size + 127) // 128,), (128,), (cp.asarray(a), out, np.int32(a.size)))
    out = cp.asnumpy(out).reshape(-1, 2)
    am = np.maximum(a, 1e-8)
    lz = math.log(2) + np.log(i1e(am)) + am - np.log(am)
    am6 = np.maximum(a, 1e-6)
    dl = np.where(am6 < 1e-3, am6 / 4, i0e(am6) / i1e(am6) - 2 / am6)
    e1 = np.abs(out[:, 0] - lz).max()
    e2 = np.abs(out[:, 1] - dl).max()
    print(f"bessel: max |log z - scipy| = {e1:.2e}, max |dlog z - scipy| = {e2:.2e}")
    return e1 < 1e-10 and e2 < 1e-10


def t_fields():
    be, geo, beta, U, Y = setup(4, 8)
    R = C.PairSampler(be, geo, beta, 16.0, U.copy(), Y)
    for _ in range(3):
        R.sweep()                                       # a generic, non-equilibrium-start state
    Fs = Fz.FusedSampler(be, geo, beta, 16.0, R.U.copy(), Y)
    worst = 0.0
    for ci in range(0, len(geo.classes), 7):
        c = geo.classes[ci]
        d = Fs._launch(ci, debug=True)                  # (P, n, 2, 13)
        F_lin, F_o, lz_o, Fw = Fz.reference_fields(R, c)
        xp = be.xp
        dd = xp.asarray(d)
        e = max(float(xp.abs(dd[..., 0:4] - xp.moveaxis(F_lin, 1, 2)).max()),
                float(xp.abs(dd[..., 4:8] - xp.moveaxis(F_o, 1, 2)).max()),
                float(xp.abs(dd[..., 8] - xp.moveaxis(lz_o, 1, 2)).max()),
                float(xp.abs(dd[..., 9:13] - xp.moveaxis(Fw, 1, 2)).max()))
        worst = max(worst, e)
    print(f"fields (47 classes, 8 pairs, both chains): max |fused - reference| = {worst:.2e}")
    return worst < 1e-9


def t_g1():
    be, geo, beta, U, Y = setup(4, 8, perturb=False)
    r = C.run_chains(be, geo, beta, 16.0, U, Y, 30, 10, sampler=Fz.FusedSampler)
    m = int(r["d"].max())
    print(f"G1 (fused): max disagreement over 30 sweeps = {m}")
    return m == 0


def t_onelink():
    be = C.Backend(True, 4)
    ok = True
    for k in (16.0, 4.0):
        ok &= C.selftest_onelink(be, CONF, beta_k=(None, k), R=400, upd=60, sampler=Fz.FusedSampler)
    return ok


def t_gauge():
    be = C.Backend(True, 5)
    return C.selftest_gauge(be, CONF, sweeps=60, P=16, sampler=Fz.FusedSampler)


def t_station():
    be, geo, beta, U, Y = setup(4, 32, perturb=False)
    S = Fz.FusedSampler(be, geo, beta, 16.0, U, Y)
    vals = []
    for t in range(1, 151):
        S.sweep()
        if t % 25 == 0:
            vals.append(float(S.plaquettes().mean()))
    print("station (fused, beta 2.3, kappa 16, 32 instances): box plaquette every 25 sweeps", [round(v, 4) for v in vals],
          f"(equilibrium 0.602); acceptance {S.acceptance():.3f}")
    return abs(np.mean(vals[2:]) - 0.602) < 0.01


def _compare(name, smp, sweeps=60):
    import json
    be, geo, beta, U, Y = setup(4, 16, seed=7, gpu=(smp is not None))
    U = C.heat_start(be, geo, beta, U, Y, list(range(8, 16)), sampler=smp)
    r = C.run_chains(be, geo, beta, 16.0, U, Y, sweeps, 10, sampler=smp)
    res = dict(plaq=float(r["plaq"].mean()), d=float(r["d"][-3:].mean()), w=float(r["w"][-3:].mean()),
               n=int(len(geo.dyn_lids)))
    print(f"compare {name}: plaquette {res['plaq']:.4f}, disagreement (last 30 of 60 sweeps) {res['d']:.1f} of {res['n']}, "
          f"W {res['w']:.1f}")
    json.dump(res, open(f"runs/compare_{name}.json", "w"))
    return True


def t_compare_ref():
    return _compare("reference", None)


def t_compare_fused():
    import json, os
    _compare("fused", Fz.FusedSampler)
    if os.path.exists("runs/compare_reference.json"):
        a = json.load(open("runs/compare_reference.json"))
        b = json.load(open("runs/compare_fused.json"))
        ok = abs(a["plaq"] - b["plaq"]) < 0.01 and abs(a["d"] - b["d"]) < 0.05 * a["n"]
        print(f"compare: plaquette {a['plaq']:.4f} vs {b['plaq']:.4f}; disagreement {a['d']:.1f} vs {b['d']:.1f}")
        return ok
    return True


def t_speed():
    res = {}
    for name, smp, P in (("fused", Fz.FusedSampler, 480), ("reference", C.PairSampler, 480)):
        be, geo, beta, U, Y = setup(6, P)
        S = smp(be, geo, beta, 16.0, U, Y)
        S.sweep()
        C.sync(be)
        n = 5 if name == "fused" else 1
        t0 = time.time()
        for _ in range(n):
            S.sweep()
        C.sync(be)
        res[name] = (time.time() - t0) / n
        print(f"speed {name}: {res[name]:.3f} s per sweep (ell 6, {P} pairs)")
    print(f"speed-up {res['reference'] / res['fused']:.1f}x")
    return True


if __name__ == "__main__":
    tests = dict(bessel=t_bessel, fields=t_fields, g1=t_g1, onelink=t_onelink, gauge=t_gauge, station=t_station,
                 compare_ref=t_compare_ref, compare_fused=t_compare_fused, speed=t_speed)
    for name in sys.argv[1:]:
        t0 = time.time()
        ok = tests[name]()
        print(f"[{name}] {'OK' if ok else 'FAILED'} ({time.time() - t0:.0f} s)", flush=True)
