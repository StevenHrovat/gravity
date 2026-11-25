# Longer adversarial search (NO-TRAP.md 3): does the maximal capture time keep growing, and what does the worst star
# approach? Same model and capture rule as notrap_search.py. Prints the worst star's relative angles and its orbit.
import sys, os
import numpy as np
R = int(sys.argv[1]) if len(sys.argv) > 1 else 100
IT = int(sys.argv[2]) if len(sys.argv) > 2 else 300
sys.argv = sys.argv[:1] + ["40", "1", "7"]
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "notrap_search.py"), encoding="utf-8").read()
src = src.split("# ---------- NT1 ----------")[0]
ns = {"__file__": os.path.abspath(__file__)}; exec(compile(src, "notrap_search.py", "exec"), ns)
qmul, qinv, qexp, spreads, step04, n = ns["qmul"], ns["qinv"], ns["qexp"], ns["spreads"], ns["step04"], ns["n"]
capture_times, haar, rng = ns["capture_times"], ns["haar"], ns["rng"]
ns["CAP"] = 80
g = haar(R); t = capture_times(g); sig = np.full(R, 0.3)
for it in range(IT):
    cand = qmul(qexp(sig[:, None, None] * rng.normal(size=g.shape[:-1] + (3,))), g)
    tc = capture_times(cand); better = tc >= t
    g[better] = cand[better]; t[better] = tc[better]
    sig = np.where(better, sig * 1.1, sig * 0.8).clip(1e-6, 1.0)
    if it % 50 == 0 or it == IT - 1:
        print(f"iteration {it:3d}: max capture {t.max()}  median {int(np.median(t))}  min step size of the best {sig[np.argmax(t)]:.1e}")
w = g[np.argmax(t)][None]
def relangles(x):
    rel = qmul(x[0][:, None, :], qinv(x[0][None, :, :]))
    return np.degrees(np.arccos(np.clip(rel[..., 0], -1, 1)))
np.set_printoptions(precision=0, suppress=True, linewidth=160)
print("worst star: relative angles (degrees) before and along its orbit")
for k in range(6):
    print(f"step {k}: spread {np.degrees(spreads(w)[0][0]):.1f} deg\n{relangles(w)}")
    w = step04(w, False)
