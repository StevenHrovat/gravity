"""Collect the bootstrap results, apply the pre-registered checks (PREREG-BOOTSTRAP.md section 3) and print the tables.

Usage (from docs/mass-gap/): py bootstrap/summarize.py file1.json file2.json ...   (files in results/, names without path are fine)
Writes results/bootstrap_summary.json.
"""

import os
os.environ['CUDA_VISIBLE_DEVICES'] = '-1'

import glob
import json
import math
import sys

from scipy.special import iv

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, '..', 'results')

MC4 = {  # pre-registered 4D plaquette references: value, error, source
    '2.3': (0.60224, 0.00006, 'results/lattice_summary.json (10^4)'),
    '2.4': (0.630002, 0.000013, 'lattice/runs-gpu/ttl_b2.4_L16.npz (16^4)'),
    '2.5': (0.651964, 0.000006, 'lattice/runs-gpu/ttl_b2.5_L20.npz (20^4)'),
}
KZ = {  # Kazakov-Zheng arXiv:2404.16925 Fig. 1b, read off the plot (+-0.01): (Lmax, beta) -> [lo, up]
    (16, '2.3'): (0.48, 0.66),
    (24, '2.3'): (0.549, 0.623),
    (24, '2.5'): (0.597, 0.656),
}


def mc_reference():
    p = os.path.join(RES, 'bootstrap_mc_reference.json')
    out = {}
    if os.path.exists(p):
        with open(p) as f:
            for r in json.load(f)['runs']:
                out[(r['d'], str(r['beta']), r['L'])] = r
    return out


def exact2d(beta, R, T):
    u = iv(2, beta) / iv(1, beta)
    return u ** (R * T)


def main():
    files = sys.argv[1:] or sorted(glob.glob(os.path.join(RES, 'bootstrap_d*_L*.json')))
    mc = mc_reference()
    if '2.0' not in MC4:
        r = mc.get((4, '2.0', 10))
        if r:
            MC4['2.0'] = (r['plaquette'][0], r['plaquette'][1], 'results/bootstrap_mc_reference.json (CPU, 10^4)')
    summary = []
    verdict_ok = True
    for fn in files:
        path = fn if os.path.exists(fn) else os.path.join(RES, fn)
        with open(path) as f:
            data = json.load(f)
        st = data['settings']
        d, L = st['d'], st['Lmax']
        tab = {}
        for r in data['results']:
            tab.setdefault((r['beta'], r['target']), {})[r['bound']] = r
        print(f'\n## d = {d}, L_max = {L} ({os.path.basename(path)}): {st["n_var"]} variables, {st["n_eq"]} equations, '
              f'{st["n_blocks"]} PSD blocks (max {st["max_block"]})')
        print('| beta | loop | lower (float) | upper (float) | lower (rigorous) | upper (rigorous) | width | reference | contained |')
        print('|---|---|---|---|---|---|---|---|---|')
        for (b, t), bb in sorted(tab.items(), key=lambda kv: (float(kv[0][0]), kv[0][1])):
            lo, up = bb.get('lower', {}), bb.get('upper', {})
            R, T = (int(v) for v in t.split('x'))
            ref, err, ok = None, None, None
            if d == 2:
                ref = exact2d(float(b), R, T)
                ok_f = lo['value'] - 1e-6 <= ref <= up['value'] + 1e-6
                ok_r = lo['rigorous'] <= ref <= up['rigorous']
                ok = ok_f and ok_r
            elif d == 4 and t == '1x1' and b in MC4:
                ref, err = MC4[b][0], MC4[b][1]
                ok_f = lo['value'] <= ref + 2 * err and up['value'] >= ref - 2 * err
                ok_r = lo['rigorous'] <= ref + 2 * err and up['rigorous'] >= ref - 2 * err
                ok = ok_f and ok_r
            elif d == 4:
                r = mc.get((4, b, 12 if b == '2.3' else 14)) or mc.get((4, b, 10))
                if r and t in r['W']:
                    ref, err = r['W'][t]
                    ok = lo['rigorous'] <= ref + 2 * err and up['rigorous'] >= ref - 2 * err
            if ok is False and (d == 2 or t == '1x1'):
                verdict_ok = False
            width = up['value'] - lo['value']
            refs = '' if ref is None else (f'{ref:.6f}' + (f' +- {err:.6f}' if err else ' (exact)'))
            print(f'| {b} | W({R},{T}) | {lo["value"]:.6f} | {up["value"]:.6f} | {lo["rigorous"]:.6f} | {up["rigorous"]:.6f} | '
                  f'{width:.6f} | {refs} | {"" if ok is None else ("yes" if ok else "NO")} |')
            kz = KZ.get((L, b)) if (d == 4 and t == '1x1') else None
            summary.append(dict(file=os.path.basename(path), d=d, Lmax=L, beta=b, loop=t, lower=lo['value'], upper=up['value'],
                                lower_rigorous=lo['rigorous'], upper_rigorous=up['rigorous'],
                                rigour_loss=max(lo['value'] - lo['rigorous'], up['rigorous'] - up['value']),
                                width=width, reference=None if ref is None else float(ref), reference_error=err,
                                contained=None if ok is None else bool(ok),
                                status=[lo.get('status'), up.get('status')],
                                kz_same_Lmax=kz, kz_overlap=(None if kz is None else (lo['rigorous'] <= kz[1] and up['rigorous'] >= kz[0]))))
    # exploratory: rigorous upper bounds on the static potential V0(R) (transfer matrix positivity, overlaps summing to 1):
    #   W(R,T) <= exp(-V0 T)  =>  V0 <= -ln(W_lo(R,T)) / T;   W(R,T+1)/W(R,T) <= exp(-V0)  =>  V0 <= ln(W_up(R,T) / W_lo(R,T+1)),
    # with W(R,0) = 1. Loops are oriented R x T; W(R,T) = W(T,R) by symmetry.
    energy = []
    groups = {}
    for row in summary:
        groups.setdefault((row['file'], row['beta']), {})[row['loop']] = row
    for (fn, b), rows in groups.items():
        for R in (1, 2):
            W = {}
            for t, row in rows.items():
                r_, t_ = (int(v) for v in t.split('x'))
                for rr, tt in ((r_, t_), (t_, r_)):
                    if rr == R:
                        W[tt] = (row['lower_rigorous'], row['upper_rigorous'])
            W[0] = (1.0, 1.0)
            best, how = float('inf'), ''
            for T, (lo, up) in W.items():
                if T > 0 and lo > 0 and -math.log(lo) / T < best:
                    best, how = -math.log(lo) / T, f'-ln W_lo({R},{T})/{T}'
                if T + 1 in W and W[T + 1][0] > 0 and up > 0 and math.log(up / W[T + 1][0]) < best:
                    best, how = math.log(up / W[T + 1][0]), f'ln W_up({R},{T})/W_lo({R},{T+1})'
            if best < float('inf'):
                energy.append(dict(file=fn, beta=b, R=R, V0_upper=best, from_=how))
                print(f'  {fn} beta={b}: V0({R}) <= {best:.4f}  ({how})')
    # exploratory: naive Creutz-ratio interval from the rigorous single bounds
    creutz = []
    for (fn, b), rows in groups.items():
        if all(k in rows for k in ('1x1', '1x2', '2x2')):
            w11, w12, w22 = rows['1x1'], rows['1x2'], rows['2x2']
            lo = (2 * math.log(w12['lower_rigorous']) - math.log(w11['upper_rigorous']) - math.log(w22['upper_rigorous'])
                  if w12['lower_rigorous'] > 0 else float('-inf'))
            up = (2 * math.log(w12['upper_rigorous']) - math.log(w11['lower_rigorous']) - math.log(w22['lower_rigorous'])
                  if min(w11['lower_rigorous'], w22['lower_rigorous']) > 0 else float('inf'))
            creutz.append(dict(file=fn, beta=b, chi2_naive=[lo, up]))
            print(f'  {fn} beta={b}: chi(2) in [{lo:.3f}, {up:.3f}] (naive interval propagation)')
    with open(os.path.join(RES, 'bootstrap_summary.json'), 'w') as f:
        json.dump(dict(validated=verdict_ok, rows=summary, static_potential_upper_bounds=energy, creutz_naive=creutz, mc4_references={k: list(v) for k, v in MC4.items()},
                       kz_readoff=[[k[0], k[1], v[0], v[1]] for k, v in KZ.items()]), f, indent=1)
    print(f'\nAll pre-registered containment checks pass: {verdict_ok}')


if __name__ == '__main__':
    main()
