"""Check B of SPEEDFIX.md: statistical comparison of the old code (actnumber_old.py, as benched) and the new code (actnumber.py) on small
lattices.  Usage:
  py speedfix_equiv.py launch OUTDIR [SEEDSHIFT]   starts old and new runs of the four groups (parallel processes), waits, then compares
  py speedfix_equiv.py compare OUTDIR              compares the npz files in OUTDIR
The configuration table and the pass rule are pre-registered in SPEEDFIX.md (section "Check B") and are not to be changed after the runs."""
import os
import subprocess
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
# name, group, beta, L, T, chains, therm, meas, every, levels, seed_old, seed_new
CONFIGS = [
    ("su2", "su2", 2.4, 4, 8, 8, 300, 300, 6, "0,2", 9001, 9002),
    ("u1", "u1", 1.1, 4, 8, 8, 300, 400, 2, "0,2", 9011, 9012),
    ("z2", "z2", 0.42, 2, 8, 8, 300, 500, 2, "0", 9021, 9022),
    ("2i", "2i", 2.4, 4, 8, 8, 100, 300, 3, "0,2", 9031, 9032),
]
NBLOCK = 10


def cmd(code, c, out, shift):
    name, g, beta, L, T, ch, th, me, ev, lv, so, sn = c
    seed = (so if code == "actnumber_old.py" else sn) + shift
    return [sys.executable, "-W", "ignore", os.path.join(HERE, code), "run", g, str(beta), str(L), str(T), str(seed), out, "--plane", "01",
            "--chains", str(ch), "--therm", str(th), "--meas", str(me), "--every", str(ev), "--levels", lv, "--path", "fused"]


def observables(path):
    d = np.load(path)
    ops = d["ops"]            # (meas, B, nlevels, T), complex for U(1)
    plaq = d["plaq"]          # (meas, B)
    sheet = d["sheet"]        # (meas, B, 2): signed sheet plaquette, bulk of the twisted plane
    obs = {"plaquette": plaq, "sheet plaquette": sheet[..., 0], "twisted-plane bulk plaquette": sheet[..., 1]}
    for li in sorted({0, ops.shape[2] - 1}):
        p = ops[:, :, li, :]
        pn = np.roll(p, -1, axis=-1)
        tag = f"level {int(d['levels'][li])}"
        obs[f"<|p|^2> {tag}"] = np.real(p * np.conj(p)).mean(axis=-1)
        obs[f"<p(t) p(t+1)> {tag}"] = np.real(p * np.conj(pn)).mean(axis=-1)
    return obs


def blocks(x):
    """x (meas, B) -> block means (B * NBLOCK)."""
    m = x.shape[0] // NBLOCK * NBLOCK
    return x[:m].reshape(NBLOCK, m // NBLOCK, x.shape[1]).mean(axis=1).ravel()


def compare(outdir):
    worst = {}
    for c in CONFIGS:
        name = c[0]
        fo, fn = os.path.join(outdir, f"{name}_old.npz"), os.path.join(outdir, f"{name}_new.npz")
        if not (os.path.exists(fo) and os.path.exists(fn)):
            print(f"{name}: missing files")
            continue
        oo, on = observables(fo), observables(fn)
        print(f"--- {name}: beta {c[2]} L {c[3]} T {c[4]}  ({np.load(fo)['ops'].shape[0]} / {np.load(fn)['ops'].shape[0]} measurements per chain)")
        for k in oo:
            bo, bn = blocks(oo[k]), blocks(on[k])
            mo, eo = bo.mean(), bo.std(ddof=1) / np.sqrt(bo.size)
            mn, en = bn.mean(), bn.std(ddof=1) / np.sqrt(bn.size)
            z = (mo - mn) / np.sqrt(eo ** 2 + en ** 2)
            worst[(name, k)] = z
            print(f"  {k:32s} old {mo: .5f} +- {eo:.5f}   new {mn: .5f} +- {en:.5f}   z = {z:+.2f}")
    az = np.abs(np.array(list(worst.values())))
    for name in [c[0] for c in CONFIGS]:
        zz = np.array([abs(z) for (n, k), z in worst.items() if n == name])
        if zz.size:
            verdict = "PASS" if (zz <= 2).all() else ("REPEAT (one value in 2..3)" if ((zz > 2).sum() == 1 and zz.max() <= 3) else "FAIL")
            print(f"{name}: max |z| = {zz.max():.2f}, {int((zz > 2).sum())} above 2 -> {verdict}")


def launch(outdir, shift):
    os.makedirs(outdir, exist_ok=True)
    procs = []
    for c in CONFIGS:
        for code, tag in (("actnumber_old.py", "old"), ("actnumber.py", "new")):
            out = os.path.join(outdir, f"{c[0]}_{tag}.npz")
            log = open(os.path.join(outdir, f"{c[0]}_{tag}.log"), "w")
            procs.append(subprocess.Popen(cmd(code, c, out, shift), stdout=log, stderr=subprocess.STDOUT, cwd=HERE))
    for p in procs:
        p.wait()
    print("runs finished, exit codes", [p.returncode for p in procs])
    compare(outdir)


if __name__ == "__main__":
    if sys.argv[1] == "launch":
        launch(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 0)
    else:
        compare(sys.argv[2])
