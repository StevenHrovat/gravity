"""Task 2 by-product: the isotropic two-coupling window (all plaquettes bF, bA, no cubic or rectangle term) with the new fundamental-channel
bound of cert_measured.py: the largest |bF| with column 18 k < 1, certified, for several |bA|. Compared with c3c's corners
(|bA|,|bF|) <= (0.21,0), (0.20,0.0020), (0.15,0.0145), (0.10,0.0265), (0.05,0.0425), (0,0.0685)."""
import json, os, sys, time
os.environ["CUDA_VISIBLE_DEVICES"] = "-1"
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cert_measured as cm

def col(bF, bA):
    c = dict(bFts=bF, bFss=bF, bAts=bA, bAss=bA, bTts=0.0, bTss=0.0, bR=0.0)
    return cm.column(c, 200)["column"]

out = {}
t0 = time.time()
for bA in (0.0, 0.002, 0.005, 0.01, 0.02, 0.03, 0.05):
    lo, hi = 0.0, 0.30
    if col(hi, bA) < 1: lo = hi
    else:
        for _ in range(14):
            m = (lo + hi) / 2
            if col(m, bA) < 1: lo = m
            else: hi = m
    lo = int(lo * 1e4) / 1e4              # round down to 1e-4
    out[str(bA)] = dict(bF_max=lo, column=col(lo, bA))
    print(f"|bA| <= {bA}: certified |bF| <= {lo:.4f} (column {out[str(bA)]['column']:.5f})  [{time.time()-t0:.0f}s]", flush=True)
json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "iso_window.json"), "w"), indent=1)
