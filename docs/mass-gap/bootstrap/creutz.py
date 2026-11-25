"""Exploratory: bounds on the Creutz ratio chi(2) = -ln[W(2,2) W(1,1) / W(1,2)^2] from the bootstrap (PREREG-BOOTSTRAP.md, section 4).

The joint allowed region of (W11, W12, W22) is outer-approximated by certified support values in 13 directions (26 SDPs, each with an
exact-arithmetic certificate); chi(2) is then bounded over that polytope by a branch-and-bound with 3-variable LPs (floating point,
tolerance ~1e-9: the polytope is rigorous, the final 3-variable optimisation is not interval-checked). The naive interval
propagation from the rigorous single bounds is reported as well.

Usage (from docs/mass-gap/): py bootstrap/creutz.py --d 4 --Lmax 12 --betas 2.3,2.4 [--procs 12] [--tag name]
Writes results/bootstrap_creutz_d{d}_L{Lmax}{_tag}.json.
"""

import os
os.environ['CUDA_VISIBLE_DEVICES'] = '-1'  # never touch the GPU (it runs other jobs); set before any other import


import argparse
import heapq
import json
import math
import os
import pickle
import sys
import time
from fractions import Fraction
from multiprocessing import Pool

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import su2boot as sb
import su2sdp as sd

K11, K12, K22 = (sb.canon(sb.rect(*rt)) for rt in ((1, 1), (1, 2), (2, 2)))
DIRS = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, -1, 0), (0, 1, 1), (0, 1, -1), (1, 0, 1), (1, 0, -1), (1, 1, 1), (1, -1, 1),
        (1, 1, -1), (-1, 1, 1)]
_PROB = None


def _init(path):
    global _PROB
    with open(path, 'rb') as f:
        _PROB = pickle.load(f)


def _job(args):
    beta_str, n, sense = args
    obj = {k: c for k, c in zip((K11, K12, K22), n) if c != 0}
    res = _PROB.solve(float(beta_str), obj, -sense)  # sense = +1: maximise n.w (support value)
    c = sd.certify(_PROB, res, beta_str)
    return dict(beta=beta_str, n=[s * v for v in n] if False else list(n), sense=sense, value=res['value'], status=res['status'],
                rigorous=c['rigorous'], residual_l1=c['residual_l1'])


def polytope_chi(H, lo=True):
    """H: list of (n, h) meaning n.w <= h. Branch and bound for min (lo) or max of chi over the polytope with w > 0."""
    A = np.array([n for n, h in H], dtype=float)
    b = np.array([h for n, h in H], dtype=float)

    def box_range(box):
        Ab = np.vstack([A, np.eye(3), -np.eye(3)])
        bb = np.concatenate([b, box[:, 1], -box[:, 0]])
        out = np.zeros((3, 2))
        pt = None
        for i in range(3):
            for s, col in ((1, 0), (-1, 1)):
                c = np.zeros(3)
                c[i] = s
                r = linprog(c, A_ub=Ab, b_ub=bb, bounds=[(None, None)] * 3, method='highs')
                if r.status != 0:
                    return None, None
                out[i, col] = r.x[i]
                pt = r.x
        return out, pt

    chi = lambda w: 2 * math.log(w[1]) - math.log(w[0]) - math.log(w[2])
    big = np.array([[1e-12, 1.0], [1e-12, 1.0], [1e-12, 1.0]])
    rng, pt = box_range(big)
    if rng is None:
        return None
    # chi -> -inf if W12 can reach 0 (minimum); chi -> +inf if W11 or W22 can reach 0 (maximum); on the region w > 0 otherwise
    if lo and rng[1, 0] <= 1e-12:
        return float('-inf')
    if not lo and min(rng[0, 0], rng[2, 0]) <= 1e-12:
        return float('inf')
    best = None
    heap = []

    def bound(r):
        if lo:
            return 2 * math.log(r[1, 0]) - math.log(r[0, 1]) - math.log(r[2, 1])
        return -(2 * math.log(r[1, 1]) - math.log(r[0, 0]) - math.log(r[2, 0]))

    heapq.heappush(heap, (bound(rng), 0, rng))
    cnt = 1
    incumbent = chi(pt) if lo else -chi(pt)
    while heap:
        bd, _, r = heapq.heappop(heap)
        if incumbent - bd < 1e-5:
            return bd if lo else -bd
        i = int(np.argmax(r[:, 1] - r[:, 0]))
        mid = 0.5 * (r[i, 0] + r[i, 1])
        for half in ((r[i, 0], mid), (mid, r[i, 1])):
            box = r.copy()
            box[i] = half
            rr, p = box_range(box)
            if rr is None:
                continue
            v = chi(p) if lo else -chi(p)
            incumbent = min(incumbent, v)
            heapq.heappush(heap, (bound(rr), cnt, rr))
            cnt += 1
        if cnt > 20000:
            break
    return (min(h[0] for h in heap) if heap else incumbent) * (1 if lo else -1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--d', type=int, default=4)
    ap.add_argument('--Lmax', type=int, default=12)
    ap.add_argument('--lpos', type=int, default=None)
    ap.add_argument('--kinds', default='G,RS,RD,RL')
    ap.add_argument('--sub-d', type=int, default=None)
    ap.add_argument('--extra-fams', default='', help='kind:lpos:sub_d,... e.g. G:8:2,RS:8:2')
    ap.add_argument('--extra-eqs', default='', help='Wmax:sub_d,... e.g. 12:2')
    ap.add_argument('--betas', default='2.3,2.4')
    ap.add_argument('--procs', type=int, default=12)
    ap.add_argument('--tag', default='')
    a = ap.parse_args()
    t0 = time.time()
    xf = [tuple([t.split(':')[0], int(t.split(':')[1])] + [None if v == 'None' else int(v) for v in t.split(':')[2:]])
          for t in a.extra_fams.split(',') if t]  # kind:lpos:sub_d[:prod]
    xe = [(int(t.split(':')[0]), int(t.split(':')[1])) for t in a.extra_eqs.split(',') if t]
    prob = sd.Problem(a.d, a.Lmax, a.lpos, tuple(a.kinds.split(',')), a.sub_d, None, extra_keys=[K11, K12, K22], extra_fams=xf, extra_eqs=xe)
    ppath = os.path.join(sd.CACHE, f'prob_creutz_{os.getpid()}.pkl')
    with open(ppath, 'wb') as f:
        pickle.dump(prob, f)
    jobs = [(b, n, s) for b in a.betas.split(',') for n in DIRS for s in (1, -1)]
    with Pool(min(a.procs, len(jobs)), initializer=_init, initargs=(ppath,)) as pool:
        res = pool.map(_job, jobs, chunksize=1)
    os.remove(ppath)
    out = dict(settings=prob.summary, directions=DIRS, support=res, chi={})
    for b in a.betas.split(','):
        H = []
        Hf = []
        single = {}
        for r in res:
            if r['beta'] != b:
                continue
            n = np.array(r['n'], dtype=float) * r['sense']
            # sense +1: max n.w <= value; sense -1: min n.w >= value  ->  (-n).w <= -value
            H.append((n, r['sense'] * r['rigorous']))
            Hf.append((n, r['sense'] * r['value']))
            if sum(abs(v) for v in r['n']) == 1:
                i = int(np.argmax(np.abs(r['n'])))
                single[(i, r['sense'])] = r['rigorous']
        lo = {i: single[(i, -1)] for i in range(3)}
        up = {i: single[(i, 1)] for i in range(3)}
        naive_lo = (2 * math.log(lo[1]) - math.log(up[0]) - math.log(up[2])) if min(lo[1], up[0], up[2]) > 0 else float('-inf')
        naive_up = (2 * math.log(up[1]) - math.log(lo[0]) - math.log(lo[2])) if min(up[1], lo[0], lo[2]) > 0 else float('inf')
        pl = polytope_chi(H, lo=True)
        pu = polytope_chi(H, lo=False)
        out['chi'][b] = dict(W11=[lo[0], up[0]], W12=[lo[1], up[1]], W22=[lo[2], up[2]], naive=[naive_lo, naive_up],
                             polytope=[pl, pu])
        print(f'beta={b}: W11 [{lo[0]:.5f},{up[0]:.5f}] W12 [{lo[1]:.5f},{up[1]:.5f}] W22 [{lo[2]:.5f},{up[2]:.5f}]  '
              f'chi(2) naive [{naive_lo:.4f},{naive_up:.4f}] polytope [{pl:.4f},{pu:.4f}]', flush=True)
    out['seconds'] = time.time() - t0
    name = f'bootstrap_creutz_d{a.d}_L{a.Lmax}' + (f'_{a.tag}' if a.tag else '') + '.json'
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'results', name), 'w') as f:
        json.dump(out, f, indent=1, default=float)
    print('wrote results/' + name)


if __name__ == '__main__':
    main()
