"""POST-HOC diagnostic (not pre-registered) of E2's failed criterion 4: the distribution of the null TV (two independent i.i.d. samples
of the same exact law, each fitted) at E2's sample sizes; compared with the jackknife-based allowance 1.5 t sigma used by criterion 4."""
import json, numpy as np, ir_condlaw as cl
rng = np.random.default_rng(777)
th = cl.flat_background_theta(cl.FIT280, False)
out = {}
for n in (4600, 7400):  # E2: about 7400 samples per ensemble, tau_int about 0.7-0.8 (effective about 7400/(2 tau) ~ 4600-7400)
    v = [cl.tv(cl.fit(cl.sample_exact(th, n, rng)), cl.fit(cl.sample_exact(th, n, rng))) for _ in range(200)]
    out[n] = {"mean": float(np.mean(v)), "sd": float(np.std(v, ddof=1)), "q95": float(np.quantile(v, 0.95))}
print(json.dumps(out))
