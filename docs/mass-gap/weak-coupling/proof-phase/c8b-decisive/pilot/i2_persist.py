"""2I persistence pilot: both sectors, loop indicator R = 5, ell = 13 (s = 3), beta = 4; 120 sweeps, 2 chains."""
import sys, numpy as np, time, warnings
warnings.filterwarnings('ignore')
sys.path.insert(0, '..'); sys.argv = ['x']
import decisive as d, tiecore as t, boundary as bd
ell = int(sys.argv_ell) if hasattr(sys, 'argv_ell') else 13
beta = 4.0
box = bd.Box(ell); ops = bd.make_ops('su2', np)
for sec in 'AB':
    U = t.tie_state('i2', box, 2, 0, sec)
    upd = t.make_tie_updater('i2', box, beta, U, 1, False)
    out = []; t0 = time.time()
    for k in range(120):
        upd.sweep(3)
        if k % 20 == 19:
            f, _ = t.tie_obs('i2', ops, upd.links(), box, beta, 0, 0.0)
            out.append(np.round(f, 2).tolist())
    print('i2', beta, ell, sec, out, round(time.time() - t0), flush=True)
