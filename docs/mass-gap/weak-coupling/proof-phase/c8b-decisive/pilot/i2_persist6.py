"""2I persistence pilot, one sector per process: python i2_persist6.py A|B beta. ell = 13 (s = 3), loop R = 5, 2 chains, 80 sweeps."""
import sys, numpy as np, time, warnings
warnings.filterwarnings('ignore')
sec, beta = sys.argv[1], float(sys.argv[2])
sys.path.insert(0, '..'); sys.argv = ['x']
import decisive as d, tiecore as t, boundary as bd
ell = 13
box = bd.Box(ell); ops = bd.make_ops('su2', np)
U = t.tie_state('i2', box, 2, 0, sec)
upd = t.make_tie_updater('i2', box, beta, U, 1, False)
out = []; t0 = time.time()
for k in range(80):
    upd.sweep(3)
    if k % 20 == 19:
        f, _ = t.tie_obs('i2', ops, upd.links(), box, beta, 0, 0.0)
        out.append(np.round(f, 2).tolist())
print('i2', beta, ell, sec, out, round(time.time() - t0), flush=True)
