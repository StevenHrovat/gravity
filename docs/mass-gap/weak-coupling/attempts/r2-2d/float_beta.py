"""PREREG step 4 (float only, not certified): the same tree flow at beta = 3 and 4. Positions i = 0..3 computed, positions
i >= 4 set to the value at i = 3 (saturation: at beta = 2 they agree with i = 3 to 1e-5). Output float_beta.json."""
import json, os, sys, time
os.environ.setdefault("CUDA_VISIBLE_DEVICES", "-1")
import numpy as np
import tree_float as T
out = {}
for beta, ls in ((3.0, (12, 13, 14, 15)), (4.0, (14, 15, 16, 17, 18))):
    F = T.Fourier(beta, 256)
    kd = T.kD(F, ls[0]).max()
    for l in ls:
        t0 = time.time()
        k = [T.kP(F, l, i).max() for i in range(4)]
        kfull = [k[min(min(i, l - 1 - i), 3)] for i in range(l)]
        gam = (2 * sum(kfull) + 2 * (l - 1) * kd + 4 * kfull[0]) / (l * (l + 1))
        sig = float(-np.log(T.ive(1, beta) / T.ive(0, beta)))
        out["%g_%d" % (beta, l)] = dict(kP=k, kD=float(kd), gamma=gam, l_sqrt_sigma=l * sig ** 0.5)
        print("beta=%g l=%d kP=%s kD=%.4f gamma=%.4f l*sqrt(sigma)=%.2f (%.0fs)" % (beta, l, ["%.3f" % v for v in k], kd, gam,
              l * sig ** 0.5, time.time() - t0), flush=True)
json.dump(out, open("float_beta.json", "w"), indent=1)
