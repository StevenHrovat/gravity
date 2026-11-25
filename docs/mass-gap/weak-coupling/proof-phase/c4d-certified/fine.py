"""Supplementary: the box column at 1/100, 1/200, 1/400, 1/1600 r-cells (resolution dependence of the certified upper bounds)."""
import os, sys, json
os.environ["CUDA_VISIBLE_DEVICES"] = "-1"
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cert_measured as cm
out = {}
for name, drop in cm.FITS.items():
    c = cm.zero(cm.BOX, drop)
    row = {n: cm.column(c, n)["column"] for n in (100, 200, 400, 1600)}
    out[name] = row
    print(name, {k: round(v, 5) for k, v in row.items()}, flush=True)
json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "fine.json"), "w"), indent=1)
