"""Margin of the certified verdicts: the largest common scale s such that the column with all coupling bounds of the box multiplied by s is
certified < 1 (bisection, certified at each step), for the box and for the central couplings; plus the budget for one more family of
centre-charged loops (m incidences per link, coupling beta): m*beta*N_F* <= 1 - column."""
import json, os, sys, time
os.environ["CUDA_VISIBLE_DEVICES"] = "-1"
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cert_measured as cm
out = {}
for name, drop in cm.FITS.items():
    for label, base in (("box", cm.BOX), ("central", cm.CENTRAL)):
        f = lambda s: cm.column(cm.zero({k: v * s for k, v in base.items()}, drop), 200)
        lo, hi = 0.5, 3.0
        for _ in range(14):
            m = (lo + hi) / 2
            if f(m)["column"] < 1: lo = m
            else: hi = m
        r1 = f(1.0)
        budget = (1 - r1["column"]) / (90 * r1["N_F"])      # extra coupling on a 90-incidence loop family (like the 1x2 rectangles)
        out[f"{name}:{label}"] = dict(column=r1["column"], scale_to_one=lo, budget_beta_90_incidence_loops=budget)
        print(f"{name:7s} {label:8s}: column {r1['column']:.5f}, largest certified common scale {lo:.4f}, budget for an extra 90-incidence loop family: beta <= {budget:.5f}", flush=True)
json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "margin.json"), "w"), indent=1)
