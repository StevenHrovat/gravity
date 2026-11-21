"""The Luescher fit as PREREG-LUSCHER.md's text specifies it ("torelon mass at each L ... first plateau"), written AFTER the data were
seen, because the pre-registered luscher.py takes the torelon mass from analyse_plateau.analyse, which reports it only when the glueball
channel also has a plateau (a condition the text does not contain; it dropped L = 8). Labelled as a post-hoc code fix wherever reported.

Usage: python luscher_torelon_only.py RUN_L6.npz RUN_L8.npz ...
"""
import json
import math
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lattice"))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from analyse_plateau import analyse  # noqa: E402
from luscher import fit  # noqa: E402

rows = []
for p in sys.argv[1:]:
    r = analyse(p)
    t = r["t_torelon"]
    if t is None:
        print(f"L={r['L']:2d}: no torelon plateau")
        continue
    m, e = r["torelon_meff"][t]
    rows.append((r["L"], m, e, t))
    print(f"L={r['L']:2d}: torelon E = {m:.4f} +- {e:.4f} (plateau at t={t})")
rows.sort()
Ls, E, dE = [x[0] for x in rows], [x[1] for x in rows], [x[2] for x in rows]
(s, c), (ds, dc), chi2, dof, pv = fit(Ls, E, dE)
dev = (c - math.pi / 3) / dc
verdict = "pass" if abs(dev) <= 2 and pv > 0.05 else ("tension" if abs(dev) <= 3 else "fail")
(sn,), (dsn,), chi2n, dofn, pvn = fit(Ls, E, dE, nambu_goto=True)
out = {"points": rows, "sigma": [s, ds], "c": [c, dc], "dev_from_pi_over_3": dev, "chi2": chi2, "dof": dof, "p": pv, "verdict": verdict,
       "nambu_goto_sigma": [sn, dsn], "nambu_goto_chi2": chi2n, "nambu_goto_dof": dofn, "nambu_goto_p": pvn}
print(json.dumps(out))
