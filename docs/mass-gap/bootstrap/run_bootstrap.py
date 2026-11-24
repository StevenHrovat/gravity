"""Run the SU(2) lattice bootstrap: lower and upper bounds on Wilson loops, floating and rigorous (exact-arithmetic certificate).

Usage (from docs/mass-gap/):
    py bootstrap/run_bootstrap.py --d 2 --Lmax 12 --betas 1,2,4 --targets 1x1,1x2,2x2 [--kinds G,RS,RD,RL] [--lpos 6] [--sub-d 3]
                                  [--procs 8] [--no-certify] [--tag name]
Writes results/bootstrap_d{d}_L{Lmax}{_tag}.json.
"""

import os
os.environ['CUDA_VISIBLE_DEVICES'] = '-1'  # never touch the GPU (it runs other jobs); set before any other import


import argparse
import json
import os
import pickle
import sys
import time
from multiprocessing import Pool

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import su2boot as sb
import su2sdp as sd

_PROB = None


def target_key(name):
    R, T = (int(v) for v in name.split('x'))
    return sb.canon(sb.rect(R, T))


def _init(path):
    global _PROB
    with open(path, 'rb') as f:
        _PROB = pickle.load(f)


def _job(args):
    beta_str, name, sense, do_cert = args
    prob = _PROB
    res = prob.solve(float(beta_str), target_key(name), sense)
    out = dict(beta=beta_str, target=name, bound='lower' if sense > 0 else 'upper', value=res['value'],
               dual_value=res['dual_value'], status=res['status'], iterations=res['iterations'], seconds=res['seconds'])
    if do_cert:
        c = sd.certify(prob, res, beta_str)
        out.update(rigorous=c['rigorous'], rigorous_exact=c['rigorous_exact'], residual_l1=c['residual_l1'],
                   seconds_certify=c['seconds'])
    print(f"  beta={beta_str} {name} {out['bound']}: {out['value']:.7f} ({out['status']}, {out['seconds']:.0f}s)"
          + (f"  rigorous {out['rigorous']:.7f}" if 'rigorous' in out else ''), flush=True)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--d', type=int, default=2)
    ap.add_argument('--Lmax', type=int, default=8)
    ap.add_argument('--lpos', type=int, default=None)
    ap.add_argument('--Wmax', type=int, default=None)
    ap.add_argument('--kinds', default='G,RS,RD,RL')
    ap.add_argument('--sub-d', type=int, default=None)
    ap.add_argument('--extra-fams', default='', help='kind:lpos:sub_d,... e.g. G:8:2,RS:8:2')
    ap.add_argument('--extra-eqs', default='', help='Wmax:sub_d,... e.g. 12:2')
    ap.add_argument('--betas', default='1,2,4')
    ap.add_argument('--targets', default='1x1')
    ap.add_argument('--procs', type=int, default=8)
    ap.add_argument('--no-certify', action='store_true')
    ap.add_argument('--tag', default='')
    a = ap.parse_args()
    t0 = time.time()
    kinds = tuple(k for k in a.kinds.split(',') if k)
    targets = a.targets.split(',')
    extra = [target_key(t) for t in targets]
    print(f'bootstrap d={a.d} Lmax={a.Lmax} lpos={a.lpos} kinds={kinds} sub_d={a.sub_d}', flush=True)
    xf = [tuple([t.split(':')[0], int(t.split(':')[1])] + [None if v == 'None' else int(v) for v in t.split(':')[2:]])
          for t in a.extra_fams.split(',') if t]  # kind:lpos:sub_d[:prod]
    xe = [(int(t.split(':')[0]), int(t.split(':')[1])) for t in a.extra_eqs.split(',') if t]
    prob = sd.Problem(a.d, a.Lmax, a.lpos, kinds, a.sub_d, a.Wmax, extra_keys=extra, extra_fams=xf, extra_eqs=xe)
    os.makedirs(sd.CACHE, exist_ok=True)
    ppath = os.path.join(sd.CACHE, f'prob_d{a.d}_L{a.Lmax}_{a.tag}_{os.getpid()}.pkl')
    with open(ppath, 'wb') as f:
        pickle.dump(prob, f)
    jobs = [(b, t, s, not a.no_certify) for b in a.betas.split(',') for t in targets for s in (1, -1)]
    with Pool(min(a.procs, len(jobs)), initializer=_init, initargs=(ppath,)) as pool:
        results = pool.map(_job, jobs, chunksize=1)
    os.remove(ppath)
    summ = dict(prob.summary)
    summ['seconds_total'] = time.time() - t0
    table = {}
    for r in results:
        table.setdefault(r['beta'], {}).setdefault(r['target'], {})[r['bound']] = r
    out = dict(settings=summ, conventions='w(C) = <(1/2) tr U_C>, S = -(beta/2) sum_p tr U_p; rigorous = exact-arithmetic dual certificate '
               '(valid given |w| <= 1 for all loops)', results=results)
    name = f'bootstrap_d{a.d}_L{a.Lmax}' + (f'_{a.tag}' if a.tag else '') + '.json'
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'results', name)
    with open(path, 'w') as f:
        json.dump(out, f, indent=1)
    print(f'wrote results/{name} ({summ["seconds_total"]:.0f}s)')
    for b, tt in table.items():
        for t, bb in tt.items():
            lo, up = bb.get('lower', {}), bb.get('upper', {})
            print(f'  beta={b} {t}: [{lo.get("value", float("nan")):.6f}, {up.get("value", float("nan")):.6f}]  rigorous '
                  f'[{lo.get("rigorous", float("nan")):.6f}, {up.get("rigorous", float("nan")):.6f}]')


if __name__ == '__main__':
    main()
