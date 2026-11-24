"""Profile of the per-sweep time of actnumber.py (SPEEDFIX.md). Usage: py profile_speedfix.py GROUP BETA L T [chains] [nsweeps]"""
import sys, time, cProfile, pstats
import numpy as np
import actnumber as A
import cupy as cp
g, beta, L, T = sys.argv[1], float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
B = int(sys.argv[5]) if len(sys.argv) > 5 else 8
n = int(sys.argv[6]) if len(sys.argv) > 6 else 20
geo = A.Geometry(L, T, (0, 1), xp=cp)
upd = A.make_updater(g, geo, beta, A.initial(g, geo, B, 1), 1, cp, path="fused")
upd.sweep(3); cp.cuda.Device().synchronize()
t = time.time()
for _ in range(n): upd.sweep(3)
cp.cuda.Device().synchronize()
print(f"{g} L={L} T={T} B={B}: {(time.time()-t)/n*1e3:.1f} ms/sweep")
pr = cProfile.Profile(); pr.enable()
for _ in range(n): upd.sweep(3)
cp.cuda.Device().synchronize()
pr.disable()
pstats.Stats(pr).sort_stats("cumtime").print_stats(18)
