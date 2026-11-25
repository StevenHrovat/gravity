import sys; sys.path.insert(0, '/mnt/project-files/gravity-v7/pt')
import numpy as np, late_patch as L
# (1) beta/H for f_PBH = 1 at delta_c 0.5 (flat-gauge threshold, as Gouttenoire-Volansky); (2) the 2025 objection: comoving delta ~ flat/10 -> flat threshold x10
need = {'1e17 g': np.log(2.3e-16), '1e19 g': np.log(2.3e-15), '1e22 g': np.log(7.3e-14)}
betas = np.array([5.5, 6.0, 6.25, 6.5, 6.75, 7.0])
lnP = []
for b in betas:
    _, _, r = L.analyse(b, dcs=(0.5,)); lnP.append(r[0.5][2]); print(f"beta/H {b}: ln P_coll {r[0.5][2]:.2f}  (G-V fit {L.fit(b,0.5):.2f})", flush=True)
lnP = np.array(lnP)
for k, v in need.items():
    print(f"f_PBH = 1 at {k}: ours beta/H = {np.interp(v, lnP[::-1], betas[::-1]):.2f}", flush=True)
print("\n2025 objection (threshold x10 in the flat-gauge delta):")
for b in (2.0, 2.5, 3.0, 4.0, 5.0, 6.0):
    _, dm, r = L.analyse(b, dcs=(4.0, 5.0, 6.67))
    print(f"beta/H {b}: " + "; ".join(f"dc {dc}: lnP {v[2]:.1f}" if v[0] is not None else f"dc {dc}: not reached" for dc, v in r.items()) + f"; max delta {dm:.1f}", flush=True)
